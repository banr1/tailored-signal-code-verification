/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.TripleRatchet.ChainKey.MessageKeysBudget
public import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core
public import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.RodataBudget
public import LibsignalBinary.Proofs.TripleRatchet.Encrypt.CoreStepEnvBudget
public import LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.CliRatchetCodeSymA
public import LibsignalBinary.Proofs.Cli.TripleRatchet.SpqrSendEmpty.CorePlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Coins.CoinsPlaced
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import ProofLib.SepLogic.WP -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `OutgoingTripleRatchet::encrypt::<Coins>` Body Proof

Threads allocator cost-model state (`RustCliAllocBudget M`) and concrete allocation envelopes across
block `428` (`OutgoingTripleRatchet::encrypt::<Coins>`) over `cliTapeAt` / `cliTapeAfter`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.TripleRatchet.Encrypt.CorePlacedBudget

open Arm64 ProofLib
open CryptoGames.CBC (blockToBytesLE bytesToBlock)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (
  ChainKey Crypto OutgoingTripleRatchet SignalMessage SignalProtocolError aesCbcEncrypt
)
open CryptoVerification (LibsignalPlacement lsLogFilterAddr lsRustDeallocSym lsmpl lsρ)
open CryptoVerification.Cli.CoinsTape (cliTapeAfter cliTapeAt)
open CryptoVerification.CliRatchet.Placed (blkLib_428 blkLib_eq_428 blkPC_428 blkPl_428)
open CryptoVerification.LibsignalSessionRepr (chainKeyBytes length_keyToBytes32)
open CryptoVerification.LibsignalTripleRatchet (
  AesCall GenerateKeysGhost OtrEncryptGhost
  SignalMessageNewGhost SpqrModel VecArg
  extHookStack extract_withLsCodeRoLoaded
  generateKeysStack messageKeysAt messageKeysStack nextChainKeyStack
  optAddrAt rootStack signalMessageNewStack
  spqrSendResultAt spqrSendStack withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.Encrypt (
  LsCallInv
  add_one_beq_zero_false_of_lt_2_63 aesCbcEncrypt_length_le_u32
  blockToBytesLE_length bytes32_unpack
  bytesToBlock_blockToBytesLE bytesToKey32_keyToBytes32
  chainKeyBytes_split chainKeyBytes_unpack errResultAt_invalidState_placed_pack
  err_branch_stack_join err_branch_stack_split lsAesEncSym lsFormatInnerSym
  lsOtrEncryptCoinsRoSym lsroCheck_otrEncryptCoinsRoSym messageKeys_seed_length
  model_of_send_none msgResultAt_ok_pack
  ok_branch_epilogue_stack otrAt_exists_pack otrAt_updated_pack
  pair_576_entails_memRegion post_copy_stack_fold post_dealloc1_copy_fold
  pre_dealloc1_stack_fold pre_nck_fold pre_nck_stack_split pre_new_stack_split
  ret120_split_err ret120_split_ok rodata_encrypt_placed_sepWPp
  sendResultAt_some_unpack signalMessageAt_unpack signalMessageWordsAt
  some_branch_pre_mk_fold some_branch_pre_mk_split
  spAligned_sub_640 srk_copy_pack stackAt_encrypt_epilogue stackAt_encrypt_prologue
  stackAt_sub vecU8At_unpack_dealloc vecU8Buf_expose_slice vecU8Spare_dealloc
  vecU8_464_unpack vecU8_544_unpack
)
open CryptoVerification.LibsignalTripleRatchet.Encrypt.EncryptCoreFacts (
  model_of_send_some_ok_eq
)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (
  UuidParser otrAt protocolAddressAt signalMessageResultAt utf8 uuidTryParse
)
open CryptoVerification.RustHeap (allocHookStack)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
  RustCliAllocBudget SeqEnv rustAllocEvents rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Heap.SpecBudget (
  AesEncEnv FormatInnerEnv aesCallPreBudget aesEncBudgetSpec
  formatInnerBudgetEnvSpec withVmPreserved
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux (
  otrEncryptPlacedSpec otrEncryptPlacedSpecQ otrEncryptPlacedSpecQF
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.SpqrSendEmpty.CorePlacedBudget (
  spqrSendCoinsPlacedSpec
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.TripleRatchet.ChainKey.MessageKeysBudget (
  MessageKeysEnv messageKeysEvents messageKeysPlacedSpec messageKeysPlacedSpecWithStack
)
open LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget (
  OtrEncryptCoreEnv OtrEncryptEnv SpqrSendBudgetEnv
  otrSignalMsgGhost signalMessageNewEvents_eq_otrSignalMsgGhost
)
open LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.RodataBudget (
  aesEnc_placed_ok dealloc_placed_ok formatInnerEnv_placed_ok
)
open LibsignalBinary.Proofs.TripleRatchet.Encrypt.CoreStepEnvBudget (
  OptVecDropEnv OtrEncryptStepEnv
  fitsEnv_aes_of_stepEnv_some fitsEnv_fmt_of_stepEnv_none
  fitsEnv_mk_of_stepEnv_some fitsEnv_new_of_stepEnv_some fitsEnv_send_of_stepEnv
  freeOnlyEvs_of_optVecDropEnv join_focus_state nextChainKeyPlacedSpec
  onPanic_of_nck_budget onPanic_of_send_budget
  optAddrAt_atState_eq_repAlloc optVecDropEnv_of_cap
  otrAt_atState_eq_repAlloc otrSignalMessageNewGhost
  protocolAddressAt_atState_eq_repAlloc shift_frame_to_post_budget
  signalMessageResultAt_atState_eq_repAlloc
)
open LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget (
  freeOnlyEvs_of_generateKeysEnv generateKeysSpec generateKeysSpecWithStack
)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget (
  SignalMessageNewEnv signalMessageNewEvents signalMessageNewSpec signalMessageNewSpecWithStack
)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem lsLogOff_eq [LibsignalPlacement] :
    lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) :=
  rfl

/-! ## Envelope-Parametric Spec and `OtrEncryptEnv` Bridge -/

/-- Envelope-parametric budget specification of CLI `OTR::encrypt::<Coins>` over `cliTapeAt` /
`cliTapeAfter`. Definitionally equal (`rfl`) to `PlacedDefsBudgetAux.otrEncryptPlacedSpec` at
`OtrEncryptEnv C S sendEnv uuidParse`. -/
def otrEncryptCoinsPlacedEnvSpec [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (EncryptEnv : OtrEncryptGhost → List AllocEvent → Prop) :
    Spec (OtrEncryptGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st (EncryptEnv x)⌝ ∗
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptPlacedSpec
        C (A.atState lim st s) ctl uuidParse S).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜EncryptEnv x evs⌝ ∗
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptPlacedSpec
        C (A.atState lim (M.stepEvents evs st) sf) ctl uuidParse S).post x s0 sf
  onPanic := fun (x, _) s0 sf =>
    ⌜((x.model C S uuidParse).1 = .error .panic ∨ S.sendPanics x.ot.pqrState x.rest) ∧
      s0.trace <+: sf.trace⌝ ∗
      anyHeap

abbrev otrEncryptCoinsPlacedStepSpec [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (SendEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop :=
      fun _ _ evs => evs = [])
    (FmtEnv : List AllocEvent → Prop := FormatInnerEnv) :
    Spec (OtrEncryptGhost × M.σ) :=
  otrEncryptCoinsPlacedEnvSpec C A lim ctl uuidParse S
    (OtrEncryptStepEnv C S uuidParse SendEnv FmtEnv)

theorem subroutine_ok_otrEncryptCoinsPlacedEnv_framed_of_imp [LibsignalPlacement]
    {M : AllocCostModel} {prog : Program} {entry : BitVec 64}
    {Q : List (BitVec 8) → List (BitVec 8) → Prop} {F : SepProp}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {uuidParse : UuidParser} {S : SpqrModel}
    {Env₁ Env₂ : OtrEncryptGhost → List AllocEvent → Prop}
    (hImp : ∀ x evs, Q x.ot.pqrState x.rest → x.ptext.length < 2 ^ 32 → Env₁ x evs → Env₂ x evs)
    (h1 : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl
        { otrEncryptCoinsPlacedEnvSpec C A lim ctl uuidParse S Env₁ with
          pre := fun (x, st) s =>
            ⌜Q x.ot.pqrState x.rest⌝ ∗ F ∗
              (otrEncryptCoinsPlacedEnvSpec C A lim ctl uuidParse S Env₁).pre (x, st) s
          post := fun (x, st) s0 sf =>
            F ∗ (otrEncryptCoinsPlacedEnvSpec C A lim ctl uuidParse S Env₁).post (x, st) s0 sf })) :
    subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl
        { otrEncryptCoinsPlacedEnvSpec C A lim ctl uuidParse S Env₂ with
          pre := fun (x, st) s =>
            ⌜Q x.ot.pqrState x.rest⌝ ∗ F ∗
              (otrEncryptCoinsPlacedEnvSpec C A lim ctl uuidParse S Env₂).pre (x, st) s
          post := fun (x, st) s0 sf =>
            F ∗ (otrEncryptCoinsPlacedEnvSpec C A lim ctl uuidParse S Env₂).post (x, st) s0 sf }) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  obtain ⟨_hcro, hm1⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [otrEncryptCoinsPlacedEnvSpec,
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptPlacedSpec] at hm1
  simp only [sepConj_assoc] at hm1
  rw [satisfies_pure_sepConj] at hm1
  obtain ⟨hQ, hm2⟩ := hm1
  rw [sepConj_left_comm F, satisfies_pure_sepConj] at hm2
  obtain ⟨hfit2, hm3⟩ := hm2
  rw [sepConj_left_comm F, satisfies_pure_sepConj] at hm3
  obtain ⟨hpure, _hmem⟩ := hm3
  have hpt : x.ptext.length < 2 ^ 32 := hpure.2.2.2.2.1
  have hfit1 : FitsEnv M lim st (Env₁ x) :=
    FitsEnv.mono (fun evs he => hImp x evs hQ hpt he) hfit2
  have hpre1 : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        { otrEncryptCoinsPlacedEnvSpec C A lim ctl uuidParse S Env₁ with
          pre := fun (x, st) s =>
            ⌜Q x.ot.pqrState x.rest⌝ ∗ F ∗
              (otrEncryptCoinsPlacedEnvSpec C A lim ctl uuidParse S Env₁).pre (x, st) s
          post := fun (x, st) s0 sf =>
            F ∗ (otrEncryptCoinsPlacedEnvSpec C A lim ctl uuidParse S Env₁).post (x, st) s0 sf }).pre
        (x, st) s0 ∗ R := by
    dsimp only [withLsCodeRoLoaded, otrEncryptCoinsPlacedEnvSpec] at hpre ⊢
    simp only [sepConj_assoc] at hpre ⊢
    exact Satisfies.mono (sepConj_mono_right (sepConj_mono_right
      (Entails.pure_left fun _ =>
        Entails.pure_right hfit1 (Entails.refl _)))) hpre
  refine h1.mono_outcome (x, st) R s0 hpc hrun hpre1 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, otrEncryptCoinsPlacedEnvSpec] at hpost ⊢
    refine Satisfies.mono (sepConj_mono_left (sepConj_mono_right ?_)) hpost
    refine Entails.sepExists_mono fun evs => ?_
    exact Entails.pure_left fun he1 =>
      Entails.pure_right (hImp x evs hQ hpt he1) (Entails.refl _)
  · right; left; exact ⟨hpan, hpost⟩
  · right; right; left; exact ⟨code, hex, hpost⟩
  · right; right; right; exact ⟨hoom, hpost⟩

/-- Protected postcondition wrapper so `simp ... only [arm64_norm]` during instruction stepping
never expands `(otrEncryptCoinsPlacedEnvSpec ...).post` inside the `SepWPp` goal. -/
def otrCoinsPostBox [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (EncryptEnv : OtrEncryptGhost → List AllocEvent → Prop)
    (x : OtrEncryptGhost) (st0 : M.σ) (s0 sf : State) : SepProp :=
  (otrEncryptCoinsPlacedEnvSpec C A lim ctl uuidParse S EncryptEnv).post (x, st0) s0 sf

theorem otrCoinsPostBox_eq [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (uuidParse : UuidParser) (S : SpqrModel)
    (EncryptEnv : OtrEncryptGhost → List AllocEvent → Prop)
    (x : OtrEncryptGhost) (st0 : M.σ) (s0 sf : State) :
    (otrEncryptCoinsPlacedEnvSpec C A lim ctl uuidParse S EncryptEnv).post (x, st0) s0 sf =
      otrCoinsPostBox C A lim ctl uuidParse S EncryptEnv x st0 s0 sf :=
  rfl

theorem sepWP_done_encrypt_coins_budget [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {ret : BitVec 64} {s0 sf : State}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {uuidParse : UuidParser} {S : SpqrModel}
    {EncryptEnv : OtrEncryptGhost → List AllocEvent → Prop}
    {x : OtrEncryptGhost} {st0 : M.σ} {evs : List AllocEvent}
    {res : Except SignalProtocolError SignalMessage}
    {ot' : OutgoingTripleRatchet (List (BitVec 8))}
    {P_f R : SepProp}
    (hpc : sf.pc = ret) (hrun : sf.status = .Running)
    (hmod : x.model C S uuidParse = (res, ot'))
    (hevs : EncryptEnv x evs)
    (hnotpan : res ≠ .error .panic)
    (htr : sf.trace = s0.trace)
    (hspatial : P_f = ((∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64,
        otrAt A.repAlloc x.o pqCap' pqPtr' ot') ∗
      signalMessageResultAt A.repAlloc (utf8 "encrypt") x.ret res ∗
      (x.ptA ↦ₛ x.ptext) ∗ optAddrAt A.repAlloc x.locA x.loc ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗
      cliTapeAfter ctl x.cur x.rest (S.draws x.ot.pqrState x.rest) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s0.sp rootStack ∗
      A.pool lim (M.stepEvents evs st0) sf) ∗ emp)
    (hsp : sf.sp = s0.sp) (hcs : CalleeSavedPreserved s0 sf) :
    SepWP prog ret sf P_f
      (fun sf' P_f' =>
        ((sf'.mem ⊨ P_f' ∗ R) →
          (sf'.mem ⊨ otrCoinsPostBox C A lim ctl uuidParse S EncryptEnv x st0 s0 sf' ∗ R)) ∧
        sf'.sp = s0.sp ∧ CalleeSavedPreserved s0 sf') := by
  refine SepWP.done hpc hrun ⟨fun hm => ?_, hsp, hcs⟩
  rw [hspatial] at hm
  simp only [sepConj_emp] at hm
  unfold otrCoinsPostBox otrEncryptCoinsPlacedEnvSpec
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptPlacedSpec
    lsLogOff
  dsimp only
  rw [hmod]
  dsimp only
  simp only [otrAt_atState_eq_repAlloc, signalMessageResultAt_atState_eq_repAlloc,
    optAddrAt_atState_eq_repAlloc, protocolAddressAt_atState_eq_repAlloc]
  dsimp only [RustCliAllocBudget.atState]
  refine Satisfies.mono (sepConj_mono_left (Entails.sepExists_intro evs)) ?_
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hevs, ⟨hnotpan, htr⟩, by simpa only [sepConj_assoc] using hm⟩

private theorem seqEnv_append {P Q : List AllocEvent → Prop} {xs ys : List AllocEvent}
    (hp : P xs) (hq : Q ys) : SeqEnv P Q (xs ++ ys) :=
  Or.inr ⟨xs, ys, rfl, hp, hq⟩

theorem otrEncryptEnv_of_stepEnv {C : Crypto} {S : SpqrModel} {uuidParse : UuidParser}
    {SendEnv : SpqrSendBudgetEnv} {x : OtrEncryptGhost} {evs : List AllocEvent}
    (h : OtrEncryptStepEnv C S uuidParse SendEnv FormatInnerEnv x evs) :
    OtrEncryptEnv C S SendEnv uuidParse x evs := by
  unfold OtrEncryptEnv OtrEncryptCoreEnv
  cases hsend : S.send x.ot.pqrState x.rest with
  | none =>
    simpa only [OtrEncryptStepEnv, hsend] using h
  | some val =>
    rcases val with ⟨newPqrState, pqrKey, pqrMsg⟩
    simp only [OtrEncryptStepEnv, hsend] at h
    rcases h with ⟨evs_spqr, evs_mk, evs_gk, evs_d2, evs_d3,
      hspqr, hmk, hgk, hd2, hd3, rfl⟩
    unfold MessageKeysEnv messageKeysEvents at hmk
    have hgk_free : FreeOnlyEvs evs_gk := freeOnlyEvs_of_generateKeysEnv hgk
    let ctLen := (x.ptext.length / 16 + 1) * 16
    let evs_new := signalMessageNewEvents uuidParse (otrSignalMessageNewGhost C x pqrKey pqrMsg)
    let evs_d1 := if x.pqCap = 0#64 then [] else rustDeallocEvents x.pqCap.toNat 1
    have hd1_free : FreeOnlyEvs evs_d1 := by
      dsimp only [evs_d1]
      split_ifs
      · exact FreeOnlyEvs.nil
      · exact FreeOnlyEvs.singleton 1 x.pqCap.toNat
    have hd_tail : FreeOnlyEvs (evs_d1 ++ (evs_d2 ++ evs_d3)) :=
      hd1_free.append ((freeOnlyEvs_of_optVecDropEnv hd2).append
        (freeOnlyEvs_of_optVecDropEnv hd3))
    have hnew_env : SignalMessageNewEnv uuidParse
        (otrSignalMsgGhost C x.ot pqrKey pqrMsg x.ptext x.loc x.rem) evs_new := by
      unfold SignalMessageNewEnv
      exact signalMessageNewEvents_eq_otrSignalMsgGhost uuidParse C x.ot pqrKey pqrMsg x.ptext
        x.loc x.rem (otrSignalMessageNewGhost C x pqrKey pqrMsg)
        rfl rfl rfl rfl rfl rfl rfl
    have hcore :
        SeqEnv (SendEnv x.ot.pqrState x.rest)
          (SeqEnv (SeqEnv (· = rustAllocEvents 32 1) FreeOnlyEvs)
            (SeqEnv (· = rustAllocEvents ctLen 1)
              (SeqEnv (SignalMessageNewEnv uuidParse
                  (otrSignalMsgGhost C x.ot pqrKey pqrMsg x.ptext x.loc x.rem))
                FreeOnlyEvs)))
          (evs_spqr ++ ((evs_mk ++ evs_gk) ++
            (rustAllocEvents ctLen 1 ++ (evs_new ++ (evs_d1 ++ (evs_d2 ++ evs_d3)))))) :=
      seqEnv_append hspqr
        (seqEnv_append (seqEnv_append hmk hgk_free)
          (seqEnv_append rfl (seqEnv_append hnew_env hd_tail)))
    simpa only [evs_new, ctLen, evs_d1, List.append_assoc] using hcore

/-! ## Block `428` Body Proofs -/

abbrev of_sepWP_lsCallInv :=
  @CryptoVerification.LibsignalTripleRatchet.Encrypt.SepWPp.of_sepWP_lsCallInv
abbrev call_frame_lsInv :=
  @CryptoVerification.LibsignalTripleRatchet.Encrypt.SepWPp.call_frame_lsInv
abbrev call_frame_lsInv_cro :=
  @CryptoVerification.LibsignalTripleRatchet.Encrypt.SepWPp.call_frame_lsInv_cro
abbrev wpp_exists_elim :=
  @CryptoVerification.LibsignalTripleRatchet.Encrypt.SepWPp.exists_elim
abbrev wpp_exists_elim_top :=
  @CryptoVerification.LibsignalTripleRatchet.Encrypt.SepWPp.exists_elim_top
abbrev wpp_false_elim :=
  @CryptoVerification.LibsignalTripleRatchet.Encrypt.SepWPp.false_elim
abbrev bv_beq_false_of_ne :=
  @CryptoVerification.LibsignalTripleRatchet.Encrypt.beq_false_of_ne

theorem checkBlockNoSvc0_428 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 blkLib_428.text = true := by
  decide +kernel

local macro "sync_seg_428 " hH:term "," mid:term "," hrun:ident : tactic => `(tactic| (
  apply sepWP_seg_ls_vm
    (Q := (blkPC_428).rebase (blkPl_428).base (hooksException $hH))
    blkLib_eq_428 checkBlockNoSvc0_428 (mid := $mid); intro _m_strip
  wp_steps
  refine SepWP.done
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm, $hrun:ident])
    fun _m_real _hnsp => ?_
  refine SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by simp (config := { decide := true }) only [arm64_norm, $hrun:ident]))
    (hnext := ?_)
  simp only [State.setMem_setMem]))

section Block428Body

attribute [local irreducible] otrCoinsPostBox

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
set_option linter.unusedSimpArgs false in
theorem otrEncrypt_coins_placed_step_body_ok_frame [LibsignalPlacement] {M : AllocCostModel}
    (Q : List (BitVec 8) → List (BitVec 8) → Prop) (F : SepProp)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (S : SpqrModel)
    (SendEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop :=
      fun _ _ evs => evs = [])
    (FmtEnv : List AllocEvent → Prop := FormatInnerEnv)
    (H : String → Option (State → State))
    (hFmtWit : ∃ evs, FmtEnv evs := by exact ⟨[], rfl⟩)
    (h_aes : HookSat H lsAesEncSym (aesEncBudgetSpec C.E M A lim))
    (h_fmt : HookSat H lsFormatInnerSym (formatInnerBudgetEnvSpec M A lim FmtEnv))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hSend : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 427)
      (withLsCodeRoLoaded lsmpl
        { spqrSendCoinsPlacedSpec M A lim ctl S (fun sc evs => SendEnv sc.st.bytes sc.rest evs) with
          pre := fun (sc, st) s =>
            ⌜Q sc.st.bytes sc.rest⌝ ∗ F ∗
              (spqrSendCoinsPlacedSpec M A lim ctl S
                (fun sc evs => SendEnv sc.st.bytes sc.rest evs)).pre (sc, st) s
          post := fun (sc, st) s0 sf =>
            F ∗ (spqrSendCoinsPlacedSpec M A lim ctl S
              (fun sc evs => SendEnv sc.st.bytes sc.rest evs)).post (sc, st) s0 sf }))
    (hMK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 38) (withLsCodeRoLoaded lsmpl (messageKeysPlacedSpec C.F A lim)))
    (hGK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 69) (withLsCodeRoLoaded lsmpl (generateKeysSpec M A lim C.F)))
    (hNew : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 63) (withLsCodeRoLoaded lsmpl (signalMessageNewSpec M A lim C.F uuidTryParse)))
    (hNCK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 39) (withLsCodeRoLoaded lsmpl (nextChainKeyPlacedSpec C.F))) :
    subroutine_ok ((blkPC_428).rebase (blkPl_428).base H) (blkPl_428).base
      (withLsCodeRoLoaded lsmpl
        { otrEncryptCoinsPlacedStepSpec C A lim ctl uuidTryParse S SendEnv FmtEnv with
          pre := fun (x, st) s =>
            ⌜Q x.ot.pqrState x.rest⌝ ∗ F ∗
              (otrEncryptCoinsPlacedStepSpec C A lim ctl uuidTryParse S SendEnv FmtEnv).pre
                (x, st) s
          post := fun (x, st) s0 sf =>
            F ∗ (otrEncryptCoinsPlacedStepSpec C A lim ctl uuidTryParse S SendEnv FmtEnv).post
              (x, st) s0 sf }) := by
  apply subroutine_ok_of_sepWPp
  rintro ⟨x, st0⟩ R s0 hpc hrun hpre hsp_align
  replace hpre := extract_withLsCodeRoLoaded hpre
  rcases hpre with ⟨hinv0, hpre⟩
  unfold State.spAligned at hsp_align
  change ∀ _, _ at *
  dsimp only [withLsCodeRoLoaded, otrEncryptCoinsPlacedStepSpec] at hpre ⊢
  simp only [otrCoinsPostBox_eq]
  dsimp only [otrEncryptCoinsPlacedEnvSpec,
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptPlacedSpec,
    lsLogOff, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Option.isSome] at hpre ⊢
  simp only [otrAt_atState_eq_repAlloc, optAddrAt_atState_eq_repAlloc,
    protocolAddressAt_atState_eq_repAlloc] at hpre
  simp only [RustCliAllocBudget.atState, sepConj_assoc] at hpre
  rw [satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hQ, hpre⟩
  rw [sepConj_left_comm F, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hfit0, hpre⟩
  rw [sepConj_left_comm F, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0_0, hx1_0, hx2_0, hx3_0, hpt_lt_32, hx4_0, hloc_ne, hx5_0⟩, hpre⟩
  refine ⟨F ∗ otrAt A.repAlloc x.o x.pqCap x.pqPtr x.ot ∗
      (x.ptA ↦ₛ x.ptext) ∗
        optAddrAt A.repAlloc x.locA x.loc ∗
          protocolAddressAt A.repAlloc x.rem x.remA ∗
            memRegion x.ret 120 ∗ cliTapeAt ctl x.cur x.rest ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
            stackAt s0.sp rootStack ∗ A.pool lim st0 s0,
    R, ?_, ?_⟩
  · wp_focus_close arm64_sep_close
  have hAes := aesEnc_placed_ok (prog := (blkPC_428).rebase (blkPl_428).base H) h_aes
  have hFmt := formatInnerEnv_placed_ok (prog := (blkPC_428).rebase (blkPl_428).base H) h_fmt
  have hDealloc := dealloc_placed_ok (prog := (blkPC_428).rebase (blkPl_428).base H) h_dealloc
  dsimp only [spqrSendCoinsPlacedSpec, messageKeysPlacedSpec, messageKeysPlacedSpecWithStack,
    generateKeysSpec, generateKeysSpecWithStack, signalMessageNewSpec, signalMessageNewSpecWithStack,
    nextChainKeyPlacedSpec, withVmPreserved,
    CryptoVerification.LibsignalTripleRatchet.Encrypt.nextChainKeyPlacedSpec,
    aesEncBudgetSpec, aesCallPreBudget, formatInnerBudgetEnvSpec, rustCliDeallocBudgetSpec,
    VecArg.at, SignalMessageNewGhost.inputsAt, Option.isSome]
    at hSend hMK hGK hNew hNCK hAes hFmt hDealloc
  simp only [sepConj_assoc, sepConj_pure_left_comm F, pure_sepConj_pure_assoc]
    at hSend hMK hGK hNew hNCK hAes hFmt hDealloc
  have ⟨hsp640, hsp640_beq⟩ := spAligned_sub_640 hsp_align
  have hfit_send : FitsEnv M lim st0 (SendEnv x.ot.pqrState x.rest) :=
    fitsEnv_send_of_stepEnv hFmtWit hfit0
  apply of_sepWP_lsCallInv hinv0 (mid := lsmpl.base 427)
  wp_simp_pre only [otrAt, stackAt_encrypt_prologue s0.sp,
    stackAt_sub (s0.sp - 640#64) (rootStack - 640) spqrSendStack,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun s8 => SepWP.exists_elim fun s16 =>
    SepWP.exists_elim fun s24 => SepWP.exists_elim fun s32 =>
    SepWP.exists_elim fun s40 => SepWP.exists_elim fun s48 =>
    SepWP.exists_elim fun s56 => SepWP.exists_elim fun s64 =>
    SepWP.exists_elim fun s72 => SepWP.exists_elim fun s80 =>
    SepWP.exists_elim fun s88 => SepWP.exists_elim fun s96 =>
    SepWP.exists_elim fun w560 => ?_
  sync_seg_428 H, (lsmpl.base 427), hrun
  apply SepWP.done
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm, hrun])
  intro hinv1
  refine call_frame_lsInv_cro
    (x := (⟨s0.sp - 408#64, ⟨x.o, x.pqCap, x.pqPtr, x.ot.pqrState⟩, x.cur, x.rest⟩, st0))
    hSend hinv1
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm, hrun])
    (by simp (config := { decide := true }) only [State.spAligned, arm64_norm, hsp_align, hsp640_beq])
    rfl rfl
    ⟨hQ,
      by simp (config := { decide := true }) only [arm64_norm, hx1_0],
      by simp (config := { decide := true }) only [arm64_norm, hx1_0],
      hfit_send⟩
    (by simp (config := { decide := true }) only [State.sp_writeReg64, State.sp_setPC, State.sp_setPState, State.sp_setMem, ite_true, ite_false]; sep_focus)
    (fun _ _ _ _ => allowPanic_not_exited)
    (fun sf _ hm => onPanic_of_send_budget (x := x) (by simp (config := { decide := true }) only [arm64_norm]) hm)
    fun s1 hpc1 hrun1 hsp1 hcs1 hinv2 => ?_
  simp only [CalleeSavedPreserved] at hcs1
  simp (config := { decide := true }) only [arm64_norm, hx0_0, hx1_0, hx2_0, hx3_0, hx4_0, hx5_0] at hpc1 hsp1 hcs1
  obtain ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, h29_1⟩ := hcs1
  simp (config := { decide := true }) only [arm64_norm]
  refine wpp_exists_elim_top fun evs_spqr => ?_
  refine SepWPp.pure_elim fun ⟨hev_spqr, hdraws, htr1, hnp1⟩ => ?_
  apply shift_frame_to_post_budget; clear hpre R; intro R
  have hnp1 : S.sendPanics x.ot.pqrState x.rest = false := by simpa using hnp1
  let st1 := M.stepEvents evs_spqr st0
  have hst1_eq : M.stepEvents evs_spqr st0 = st1 := rfl
  simp only [hst1_eq]
  refine SepWPp.fold
    (Entails.of_eq (stackAt_sub (s0.sp - 640#64) (rootStack - 640) spqrSendStack).symm)
    (by sep_focus) ?_
  cases hsend : S.send x.ot.pqrState x.rest with
  | none =>
    have hfit_fmt : FitsEnv M lim st1 FmtEnv :=
      fitsEnv_fmt_of_stepEnv_none hsend hev_spqr hfit0
    simp (disch := decide) only [spqrSendResultAt, bv_sub_add_lit, Nat.reduceSub, sepConj_assoc]
    apply of_sepWP_lsCallInv hinv2 (mid := lsρ lsFormatInnerSym)
    refine SepWP.fold (Entails.of_eq (err_branch_stack_split s0.sp)) (by sep_focus) ?_
    wp_simp_pre only [stackAt_sub (s0.sp - 640#64) (rootStack - 640) extHookStack,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWP.exists_elim fun b1 => SepWP.exists_elim fun b0 =>
      SepWP.exists_elim fun c2 => SepWP.exists_elim fun c1 =>
      SepWP.exists_elim fun c0 => SepWP.exists_elim fun a2 =>
      SepWP.exists_elim fun a1 => SepWP.exists_elim fun a0 => ?_
    sync_seg_428 H, (lsρ lsFormatInnerSym), hrun1
    apply SepWP.done
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm, hrun1])
    intro hinv3
    refine call_frame_lsInv
      (x := (s0.sp - 544#64, st1))
      hFmt hinv3
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm, hrun1])
      (by simp (config := { decide := true }) only [State.spAligned, arm64_norm, hsp1, hsp_align, hsp640_beq])
      rfl rfl
      ⟨by simp (config := { decide := true }) only [arm64_norm, hsp1], hfit_fmt⟩
      (by simp (config := { decide := true }) only [State.sp_writeReg64, State.sp_writeVReg128, State.sp_setPC, State.sp_setPState, State.sp_setMem, ite_true, ite_false, hsp1]; sep_focus)
      (fun _ _ _ _ => allowPanic_not_exited)
      (fun sf _ hm => by
        simp only [sepConj_assoc, satisfies_pure_sepConj] at hm
        exact hm.1.elim)
      fun s2 hpc2 hrun2 hsp2 hcs2 hinv4 => ?_
    simp only [CalleeSavedPreserved] at hcs2
    simp (config := { decide := true }) only [arm64_norm, hsp1, h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, h29_1] at hpc2 hsp2 hcs2
    obtain ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, h29_2⟩ := hcs2
    refine wpp_exists_elim fun evs_fmt => ?_
    simp (config := { decide := true }) only [arm64_norm, hsp1, htr1]
    refine wpp_exists_elim_top fun fBs => ?_
    refine SepWPp.pure_elim fun ⟨htr2, hev_fmt⟩ => ?_
    refine SepWPp.fold
      (Entails.of_eq (stackAt_sub (s0.sp - 640#64) (rootStack - 640) extHookStack).symm)
      (by sep_focus) ?_
    apply rodata_encrypt_placed_sepWPp lsroCheck_otrEncryptCoinsRoSym hinv4.2
    apply SepWPp.of_sepWP_ret
    refine SepWP.fold (vecU8_544_unpack A.repAlloc s0.sp fBs) (by sep_focus) ?_
    wp_simp_pre only [ret120_split_err x.ret,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWP.exists_elim fun r6 => SepWP.exists_elim fun r5 =>
      SepWP.exists_elim fun r4 => SepWP.exists_elim fun r3 =>
      SepWP.exists_elim fun r2 => SepWP.exists_elim fun r1 =>
      SepWP.exists_elim fun r0 => SepWP.exists_elim fun fCap =>
      SepWP.exists_elim fun fPtr => ?_
    apply sepWP_seg_ls_vm
      (Q := (blkPC_428).rebase (blkPl_428).base (hooksException H))
      blkLib_eq_428 checkBlockNoSvc0_428 (mid := s0.readReg64 Reg.lr); intro _m_strip2
    wp_steps
    refine SepWP.done
      (by simp (config := { decide := true }) only [arm64_norm, h29_2])
      (by simp (config := { decide := true }) only [arm64_norm, hrun2])
      fun _m_real2 _hnsp2 => ?_
    refine SepWP.transport_budgetPool
      (_hnsp2.toVmPreserved (by simp (config := { decide := true }) only [arm64_norm, hrun2]))
      (hnext := ?_)
    simp only [State.setMem_setMem]
    refine SepWP.fold (err_branch_stack_join s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
    refine SepWP.fold (stackAt_encrypt_epilogue s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
    refine SepWP.fold (otrAt_exists_pack A.repAlloc x.o x.pqCap x.pqPtr x.ot) (by sep_focus) ?_
    refine SepWP.fold
      (errResultAt_invalidState_placed_pack A.repAlloc x.ret fCap fPtr fBs (lsmpl.ρ lsOtrEncryptCoinsRoSym))
      (by sep_focus) ?_
    have hst_none : M.stepEvents evs_fmt st1 = M.stepEvents (evs_spqr ++ evs_fmt) st0 :=
      (M.stepEvents_append evs_spqr evs_fmt st0).symm
    rw [hst_none]
    have hev_none : OtrEncryptStepEnv C S uuidTryParse SendEnv FmtEnv x (evs_spqr ++ evs_fmt) := by
      simp only [OtrEncryptStepEnv, hsend]
      exact Or.inr ⟨evs_spqr, evs_fmt, rfl, hev_spqr, hev_fmt⟩
    apply sepWP_done_encrypt_coins_budget
      (by simp (config := { decide := true }) only [arm64_norm, h29_2])
      (by simp (config := { decide := true }) only [arm64_norm, hrun2])
      (model_of_send_none x C S hnp1 hsend)
      hev_none
      (by decide)
      (by simp (config := { decide := true }) only [arm64_norm, htr2])
      (by sep_focus)
      (by simp (config := { decide := true }) only [arm64_norm, hsp2, BitVec.sub_add_cancel])
      (by simp only [CalleeSavedPreserved]; simp (config := { decide := true }) only [arm64_norm, h29_2])
  | some val =>
    obtain ⟨newPqrState, pqrKey, pqrMsg⟩ := val
    have hfit_mk : FitsEnv M lim st1 MessageKeysEnv :=
      fitsEnv_mk_of_stepEnv_some hsend hev_spqr hfit0
    refine SepWPp.fold (sendResultAt_some_unpack A.repAlloc s0.sp newPqrState pqrKey pqrMsg) (by sep_focus) ?_
    refine wpp_exists_elim fun newPqrCap => wpp_exists_elim fun newPqrPtr =>
      wpp_exists_elim fun pqrMsgCap => wpp_exists_elim fun pqrMsgPtr =>
      wpp_exists_elim fun k0 => wpp_exists_elim fun k1 =>
      wpp_exists_elim fun k2 => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hpqrMsgLen, hnewPqrCap⟩ => ?_
    have ⟨hnewPqrCap_beq, hnewPqrCap_eq⟩ := add_one_beq_zero_false_of_lt_2_63 hnewPqrCap
    apply of_sepWP_lsCallInv hinv2 (mid := lsmpl.base 38)
    refine SepWP.fold (Entails.of_eq (some_branch_pre_mk_split s0.sp)) (by sep_focus) ?_
    wp_simp_pre only [stackAt_sub (s0.sp - 640#64) (rootStack - 640) messageKeysStack,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWP.exists_elim fun u128 => SepWP.exists_elim fun u136 =>
      SepWP.exists_elim fun u144 => SepWP.exists_elim fun w568 =>
      SepWP.exists_elim fun w576 => SepWP.exists_elim fun w584 =>
      SepWP.exists_elim fun w592 => SepWP.exists_elim fun w600 =>
      SepWP.exists_elim fun w608 => SepWP.exists_elim fun w616 =>
      SepWP.exists_elim fun w624 => SepWP.exists_elim fun w632 =>
      SepWP.exists_elim fun w640 => ?_
    sync_seg_428 H, (lsmpl.base 38), hrun1
    refine SepWP.fold (some_branch_pre_mk_fold A.repAlloc s0.sp _ _ _ _ _ _ k0 k1 k2 pqrKey) (by sep_focus) ?_
    apply SepWP.done
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm, hrun1])
    intro hinv3
    refine call_frame_lsInv_cro
      (x := ((x.o + 152#64, x.ot.senderChainKey, s0.sp - 408#64), st1))
      hMK hinv3
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm, hrun1])
      (by simp (config := { decide := true }) only [State.spAligned, arm64_norm, hsp1, hsp_align, hsp640_beq])
      rfl rfl
      ⟨by simp (config := { decide := true }) only [arm64_norm, hsp1, h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, h29_1],
        by simp (config := { decide := true }) only [arm64_norm, hsp1, h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, h29_1],
        hfit_mk⟩
      (by simp (config := { decide := true }) only [State.sp_writeReg64, State.sp_writeVReg128, State.sp_setPC, State.sp_setPState, State.sp_setMem, ite_true, ite_false, hsp1]; sep_focus)
      (fun _ _ _ _ => allowPanic_not_exited)
      (fun sf _ hm => by
        simp only [sepConj_assoc, satisfies_pure_sepConj] at hm
        exact hm.1.elim)
      fun s2 hpc2 hrun2 hsp2 hcs2 hinv4 => ?_
    simp only [CalleeSavedPreserved] at hcs2
    simp (config := { decide := true }) only [arm64_norm, hsp1, h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, h29_1] at hpc2 hsp2 hcs2
    obtain ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, h29_2⟩ := hcs2
    refine wpp_exists_elim fun evs_mk => ?_
    simp (config := { decide := true }) only [arm64_norm, hsp1, htr1]
    refine SepWPp.pure_elim fun ⟨htr2, hev_mk⟩ => ?_
    let st2 := M.stepEvents evs_mk st1
    have hst2_eq : M.stepEvents evs_mk st1 = st2 := rfl
    simp only [hst2_eq]
    refine SepWPp.fold
      (Entails.of_eq (stackAt_sub (s0.sp - 640#64) (rootStack - 640) messageKeysStack).symm)
      (by sep_focus) ?_
    apply of_sepWP_lsCallInv hinv4 (mid := lsmpl.base 69)
    wp_simp_pre only [stackAt_sub (s0.sp - 640#64) (rootStack - 640) generateKeysStack,
      sepConj_assoc]
    sync_seg_428 H, (lsmpl.base 69), hrun2
    apply SepWP.done
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm, hrun2])
    intro hinv5
    have hseed_len : (x.ot.senderChainKey.messageKeys C.F).seed.length = 32 :=
      messageKeys_seed_length C.F x.ot.senderChainKey
    let g_gk_call : GenerateKeysGhost :=
      ⟨s0.sp - 408#64, x.ot.senderChainKey.messageKeys C.F, s0.sp - 144#64, pqrKey, s0.sp - 552#64⟩
    refine call_frame_lsInv_cro
      (x := (g_gk_call, st2))
      hGK hinv5
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm, hrun2])
      (by simp (config := { decide := true }) only [State.spAligned, arm64_norm, hsp2, hsp_align, hsp640_beq])
      rfl rfl
      ⟨by simp (config := { decide := true }) only [g_gk_call, arm64_norm, hsp2, h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, h29_2],
        by simp (config := { decide := true }) only [g_gk_call, arm64_norm, hsp2, h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, h29_2],
        by simp (config := { decide := true }) only [g_gk_call, arm64_norm, hsp2, h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, h29_2],
        hseed_len⟩
      (by simp (config := { decide := true }) only [g_gk_call, State.sp_writeReg64, State.sp_setPC, State.sp_setPState, State.sp_setMem, ite_true, ite_false, hsp2]; sep_focus)
      (fun _ _ _ _ => allowPanic_not_exited)
      (fun sf _ hm => by
        simp only [sepConj_assoc, satisfies_pure_sepConj] at hm
        exact hm.1.elim)
      fun s3 hpc3 hrun3 hsp3 hcs3 hinv6 => ?_
    simp only [CalleeSavedPreserved] at hcs3
    simp (config := { decide := true }) only [arm64_norm, hsp2, h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, h29_2] at hpc3 hsp3 hcs3
    obtain ⟨h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, h29_3⟩ := hcs3
    refine wpp_exists_elim fun evs_gk => ?_
    simp (config := { decide := true }) only [g_gk_call, arm64_norm, hsp2, htr2]
    refine SepWPp.pure_elim fun ⟨htr3, hev_gk⟩ => ?_
    let st3 := M.stepEvents evs_gk st2
    have hst3_eq : M.stepEvents evs_gk st2 = st3 := rfl
    simp only [hst3_eq]
    refine SepWPp.fold
      (Entails.of_eq (stackAt_sub (s0.sp - 640#64) (rootStack - 640) generateKeysStack).symm)
      (by sep_focus) ?_
    set mk := (x.ot.senderChainKey.messageKeys C.F).generateKeys C.F pqrKey
    apply of_sepWP_lsCallInv hinv6 (mid := lsρ lsAesEncSym)
    wp_simp_pre only [messageKeysAt, bv_sub_add_lit, Nat.reduceSub,
      stackAt_sub (s0.sp - 640#64) (rootStack - 640) extHookStack, sepConj_assoc]
    sync_seg_428 H, (lsρ lsAesEncSym), hrun3
    apply SepWP.done
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm, hrun3])
    intro hinv7
    have hpt_lt_40 : x.ptext.length < 2 ^ 40 := by omega
    let x_aes : AesCall :=
      ⟨x.ptA, x.ptext, s0.sp - 552#64, keyToBytes32 mk.cipherKey,
        s0.sp - 488#64, blockToBytesLE mk.iv, s0.sp - 464#64⟩
    have hfit_aes : FitsEnv M lim st3 (AesEncEnv x_aes) :=
      fitsEnv_aes_of_stepEnv_some hsend hev_spqr hev_mk rfl hev_gk rfl hfit0
    refine call_frame_lsInv
      (x := (x_aes, st3))
      hAes hinv7
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm, hrun3])
      (by simp (config := { decide := true }) only [State.spAligned, arm64_norm, hsp3, hsp_align, hsp640_beq])
      rfl rfl
      ⟨by simp (config := { decide := true }) only [x_aes, arm64_norm, hsp3, h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, h29_3],
        by simp (config := { decide := true }) only [x_aes, arm64_norm, hsp3, h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, h29_3, hx3_0],
        by simp (config := { decide := true }) only [x_aes, arm64_norm, hsp3],
        by simp (config := { decide := true }) only [x_aes, arm64_norm, hsp3],
        by simp (config := { decide := true }) only [x_aes, arm64_norm, hsp3],
        by simp (config := { decide := true }) only [x_aes, arm64_norm, hsp3],
        by simp (config := { decide := true }) only [x_aes, arm64_norm, hsp3],
        length_keyToBytes32 mk.cipherKey, blockToBytesLE_length mk.iv, hpt_lt_40, hfit_aes⟩
      (by simp (config := { decide := true }) only [x_aes, State.sp_writeReg64, State.sp_setPC, State.sp_setPState, State.sp_setMem, ite_true, ite_false, hsp3]; sep_focus)
      (fun _ _ _ _ => allowPanic_not_exited)
      (fun sf _ hm => by
        simp only [sepConj_assoc, satisfies_pure_sepConj] at hm
        exact hm.1.elim)
      fun s4 hpc4 hrun4 hsp4 hcs4 hinv8 => ?_
    simp only [CalleeSavedPreserved] at hcs4
    simp (config := { decide := true }) only [arm64_norm, hsp3, h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, h29_3] at hpc4 hsp4 hcs4
    obtain ⟨h19_4, h20_4, h21_4, h22_4, h23_4, h24_4, h25_4, h26_4, h27_4, h28_4, h29_4⟩ := hcs4
    refine wpp_exists_elim fun evs_aes => ?_
    simp (config := { decide := true }) only [x_aes, AesCall.frame, bytesToKey32_keyToBytes32,
      bytesToBlock_blockToBytesLE, arm64_norm, hsp3, htr3]
    refine SepWPp.pure_elim fun ⟨htr4, hev_aes⟩ => ?_
    let st4 := M.stepEvents evs_aes st3
    have hst4_eq : M.stepEvents evs_aes st3 = st4 := rfl
    simp only [hst4_eq]
    refine SepWPp.fold
      (Entails.of_eq (stackAt_sub (s0.sp - 640#64) (rootStack - 640) extHookStack).symm)
      (by sep_focus) ?_
    set ctext := aesCbcEncrypt C.E mk.cipherKey mk.iv x.ptext
    refine SepWPp.fold (vecU8_464_unpack A.repAlloc s0.sp ctext) (by sep_focus) ?_
    refine wpp_exists_elim fun ctCap => wpp_exists_elim fun ctPtr => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hctLenLeCap, hctCapLt, hctPtrNe⟩ => ?_
    have ⟨hctCap_beq, hctCap_eq⟩ := add_one_beq_zero_false_of_lt_2_63 hctCapLt
    refine SepWPp.fold (vecU8Buf_expose_slice A.repAlloc pqrMsgCap pqrMsgPtr pqrMsg) (by sep_focus) ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hpqrMsgLenLeCap, hpqrMsgCapLt, hpqrMsgPtrNe⟩ => ?_
    refine SepWPp.fold
      (bytes32_unpack (x.o + 24#64) (bs := x.ot.senderRatchetKey.publicKey.bytes.toList)
        (List.Vector.toList_length _))
      (by sep_focus) ?_
    refine wpp_exists_elim fun srk0 => wpp_exists_elim fun srk1 =>
      wpp_exists_elim fun srk2 => wpp_exists_elim fun srk3 => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hsrk => ?_
    apply of_sepWP_lsCallInv hinv8 (mid := lsmpl.base 63)
    refine SepWP.fold (Entails.of_eq (pre_new_stack_split s0.sp)) (by sep_focus) ?_
    wp_simp_pre only [chainKeyBytes_split (x.o + 152#64) x.ot.senderChainKey,
      BitVec.add_assoc, BitVec.reduceAdd,
      stackAt_sub (s0.sp - 640#64) (rootStack - 640) signalMessageNewStack,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWP.exists_elim fun d3 => SepWP.exists_elim fun d2 =>
      SepWP.exists_elim fun d1 => SepWP.exists_elim fun d0 => ?_
    sync_seg_428 H, (lsmpl.base 63), hrun4
    refine SepWP.fold
      (srk_copy_pack x.o s0.sp x.ot.senderRatchetKey.publicKey.bytes.toList srk0 srk1 srk2 srk3 hsrk)
      (by sep_focus) ?_
    apply SepWP.done
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm, hrun4])
    intro hinv9
    have hct_le : ctext.length ≤ 2 ^ 32 :=
      aesCbcEncrypt_length_le_u32 C.E mk.cipherKey mk.iv x.ptext (by omega)
    let x_new : SignalMessageNewGhost :=
      { messageVersion := x.ot.sessionVersion
        macKeyA := s0.sp - 520#64
        macKey := mk.macKey
        locA := x.locA
        loc := x.loc
        remA := x.remA
        rem := x.rem
        senderRatchetKeyA := s0.sp - 288#64
        senderRatchetKey := x.ot.senderRatchetKey.publicKey
        counter := x.ot.senderChainKey.index
        previousCounter := x.ot.previousCounter
        ciphertextA := ctPtr
        ciphertext := ctext
        senderIkA := x.o + 88#64
        senderIk := x.ot.localIdentityKey
        receiverIkA := x.o + 120#64
        receiverIk := x.ot.remoteIdentityKey
        pqRatchetA := pqrMsgPtr
        pqRatchet := pqrMsg
        ret := s0.sp - 408#64 }
    have hfit_new : FitsEnv M lim st4 (SignalMessageNewEnv uuidTryParse x_new) :=
      fitsEnv_new_of_stepEnv_some hsend hev_spqr hev_mk rfl hev_gk rfl hev_aes rfl hfit0
    refine call_frame_lsInv_cro
      (x := (x_new, st4))
      hNew hinv9
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm, hrun4])
      (by simp (config := { decide := true }) only [State.spAligned, arm64_norm, hsp4, hsp_align, hsp640_beq])
      rfl rfl
      ⟨by simp (config := { decide := true }) only [x_new, arm64_norm, hsp4, h19_4, h20_4, h21_4, h22_4, h23_4, h24_4, h25_4, h26_4, h27_4, h28_4, h29_4],
        by simp (config := { decide := true }) only [x_new, arm64_norm, hsp4, h19_4, h20_4, h21_4, h22_4, h23_4, h24_4, h25_4, h26_4, h27_4, h28_4, h29_4],
        by simp (config := { decide := true }) only [x_new, arm64_norm, hsp4, h19_4, h20_4, h21_4, h22_4, h23_4, h24_4, h25_4, h26_4, h27_4, h28_4, h29_4],
        by simp (config := { decide := true }) only [x_new, Option.isSome, arm64_norm, hsp4, h19_4, h20_4, h21_4, h22_4, h23_4, h24_4, h25_4, h26_4, h27_4, h28_4, h29_4],
        hloc_ne,
        by simp (config := { decide := true }) only [x_new, arm64_norm, hsp4, h19_4, h20_4, h21_4, h22_4, h23_4, h24_4, h25_4, h26_4, h27_4, h28_4, h29_4],
        by simp (config := { decide := true }) only [x_new, arm64_norm, hsp4, h19_4, h20_4, h21_4, h22_4, h23_4, h24_4, h25_4, h26_4, h27_4, h28_4, h29_4],
        by simp (config := { decide := true }) only [x_new, arm64_norm, hsp4, h19_4, h20_4, h21_4, h22_4, h23_4, h24_4, h25_4, h26_4, h27_4, h28_4, h29_4],
        by simp (config := { decide := true }) only [x_new, arm64_norm, hsp4, h19_4, h20_4, h21_4, h22_4, h23_4, h24_4, h25_4, h26_4, h27_4, h28_4, h29_4],
        by simp (config := { decide := true }) only [x_new, arm64_norm, hsp4, h19_4, h20_4, h21_4, h22_4, h23_4, h24_4, h25_4, h26_4, h27_4, h28_4, h29_4],
        hct_le, hpqrMsgLen, hfit_new,
        by simp (config := { decide := true }) only [wp_norm, arm64_norm]⟩
      (by simp (config := { decide := true }) only [x_new, State.sp_writeReg64, State.sp_writeVReg128, State.sp_setPC, State.sp_setPState, State.sp_setMem, ite_true, ite_false, hsp4, bv_sub_add_lit, Nat.reduceSub]; sep_focus)
      (fun _ _ _ _ => allowPanic_not_exited)
      (fun sf _ hm => by
        simp only [sepConj_assoc, satisfies_pure_sepConj] at hm
        exact hm.1.elim)
      fun s5 hpc5 hrun5 hsp5 hcs5 hinv10 => ?_
    simp only [CalleeSavedPreserved] at hcs5
    simp (config := { decide := true }) only [arm64_norm, hsp4, h19_4, h20_4, h21_4, h22_4, h23_4, h24_4, h25_4, h26_4, h27_4, h28_4, h29_4] at hpc5 hsp5 hcs5
    obtain ⟨h19_5, h20_5, h21_5, h22_5, h23_5, h24_5, h25_5, h26_5, h27_5, h28_5, h29_5⟩ := hcs5
    let evs_new := signalMessageNewEvents uuidTryParse (otrSignalMessageNewGhost C x pqrKey pqrMsg)
    let st5 := M.stepEvents evs_new st4
    have hst5_eq : M.stepEvents (signalMessageNewEvents uuidTryParse x_new) st4 = st5 := rfl
    simp only [hst5_eq]
    simp (config := { decide := true }) only [x_new, arm64_norm, hsp4, htr4]
    refine wpp_exists_elim_top fun msgG => ?_
    refine SepWPp.pure_elim fun htr5 => ?_
    refine SepWPp.fold
      (Entails.of_eq (stackAt_sub (s0.sp - 640#64) (rootStack - 640) signalMessageNewStack).symm)
      (by sep_focus) ?_
    set msg := SignalMessageNewGhost.model C.F uuidTryParse x_new
    refine SepWPp.fold (signalMessageAt_unpack A.repAlloc msgG (s0.sp - 408#64) msg) (by sep_focus) ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hmsgPqCap => ?_
    have ⟨hmsgPqCap_beq, hmsgPqCap_eq⟩ := add_one_beq_zero_false_of_lt_2_63 hmsgPqCap
    refine wpp_exists_elim fun m7 => wpp_exists_elim fun m8 =>
      wpp_exists_elim fun m9 => wpp_exists_elim fun m10 =>
      wpp_exists_elim fun m11 => wpp_exists_elim fun m12 =>
      wpp_exists_elim fun m14 => ?_
    apply of_sepWP_lsCallInv hinv10 (mid := lsmpl.base 39)
    refine SepWP.fold (Entails.of_eq (pre_nck_stack_split s0.sp)) (by sep_focus) ?_
    wp_simp_pre only [signalMessageWordsAt,
      bv_sub_add_lit, Nat.reduceSub,
      stackAt_sub (s0.sp - 640#64) (rootStack - 640) nextChainKeyStack,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWP.exists_elim fun t13 => SepWP.exists_elim fun t12 =>
      SepWP.exists_elim fun t11 => SepWP.exists_elim fun t10 =>
      SepWP.exists_elim fun t9 => SepWP.exists_elim fun t8 =>
      SepWP.exists_elim fun t7 => SepWP.exists_elim fun t6 =>
      SepWP.exists_elim fun t5 => SepWP.exists_elim fun t4 =>
      SepWP.exists_elim fun t3 => SepWP.exists_elim fun t2 =>
      SepWP.exists_elim fun t1 => SepWP.exists_elim fun t0 =>
      SepWP.exists_elim fun e2 => SepWP.exists_elim fun e1 =>
      SepWP.exists_elim fun e0 => ?_
    sync_seg_428 H, (lsmpl.base 39), hrun5
    refine SepWP.fold
      (pre_nck_fold s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
      (by sep_focus) ?_
    refine SepWP.fold
      (Entails.of_eq (chainKeyBytes_split (x.o + 152#64) x.ot.senderChainKey).symm)
      (by sep_focus) ?_
    apply SepWP.done
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm, hrun5])
    intro hinv11
    refine call_frame_lsInv_cro
      (x := (x.o + 152#64, x.ot.senderChainKey, s0.sp - 408#64))
      hNCK hinv11
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm, hrun5])
      (by simp (config := { decide := true }) only [State.spAligned, arm64_norm, hsp5, hsp_align, hsp640_beq])
      rfl rfl
      ⟨by simp (config := { decide := true }) only [arm64_norm, hsp5, h19_5, h20_5, h21_5, h22_5, h23_5, h24_5, h25_5, h26_5, h27_5, h28_5, h29_5],
        by simp (config := { decide := true }) only [arm64_norm, hsp5, h19_5, h20_5, h21_5, h22_5, h23_5, h24_5, h25_5, h26_5, h27_5, h28_5, h29_5]⟩
      (by simp (config := { decide := true }) only [State.sp_writeReg64, State.sp_writeVReg128, State.sp_setPC, State.sp_setPState, State.sp_setMem, ite_true, ite_false, hsp5]; sep_focus)
      (fun _ _ _ _ => allowPanic_not_exited)
      (fun sf _ hm => onPanic_of_nck_budget hsend (by simp (config := { decide := true }) only [arm64_norm, htr5]) hm)
      fun s6 hpc6 hrun6 hsp6 hcs6 hinv12 => ?_
    simp only [CalleeSavedPreserved] at hcs6
    simp (config := { decide := true }) only [arm64_norm, hsp5, h19_5, h20_5, h21_5, h22_5, h23_5, h24_5, h25_5, h26_5, h27_5, h28_5, h29_5] at hpc6 hsp6 hcs6
    obtain ⟨h19_6, h20_6, h21_6, h22_6, h23_6, h24_6, h25_6, h26_6, h27_6, h28_6, h29_6⟩ := hcs6
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hvm_nck, hnck_not_panic, htr6_raw⟩ => ?_
    refine SepWPp.transport_budgetPool hvm_nck (hnext := ?_)
    have htr6 : s6.trace = s0.trace := by
      simpa (config := { decide := true }) only [arm64_norm, htr5] using htr6_raw
    simp (config := { decide := true }) only [arm64_norm, hsp5]
    refine SepWPp.fold
      (Entails.of_eq (stackAt_sub (s0.sp - 640#64) (rootStack - 640) nextChainKeyStack).symm)
      (by sep_focus) ?_
    cases hnck : ChainKey.nextChainKey C.F x.ot.senderChainKey with
    | error e =>
      dsimp only
      rw [← sepConj_assoc (stackAt (s0.sp - 640#64) (rootStack - 640)) (A.pool lim st5 s6)]
      exact wpp_false_elim
    | ok ck' =>
      dsimp only
      refine SepWPp.fold (chainKeyBytes_unpack (s0.sp - 408#64) ck') (by sep_focus) ?_
      refine wpp_exists_elim fun ck0 => wpp_exists_elim fun ck1 =>
        wpp_exists_elim fun ck2 => wpp_exists_elim fun ck3 => ?_
      simp (disch := decide) only [bv_sub_add_lit, Nat.reduceSub, sepConj_assoc]
      refine SepWPp.pure_elim fun hck => ?_
      refine SepWPp.fold (chainKeyBytes_unpack (x.o + 152#64) x.ot.senderChainKey) (by sep_focus) ?_
      refine wpp_exists_elim fun ock0 => wpp_exists_elim fun ock1 =>
        wpp_exists_elim fun ock2 => wpp_exists_elim fun ock3 => ?_
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      refine SepWPp.pure_elim fun _ => ?_
      refine SepWPp.fold (vecU8At_unpack_dealloc A.repAlloc x.o x.pqCap x.pqPtr x.ot.pqrState) (by sep_focus) ?_
      refine SepWPp.fold
        (pre_dealloc1_stack_fold s0.sp _ _ _ _ _ _ mk
          x.ot.senderRatchetKey.publicKey.bytes.toList (List.Vector.toList_length _))
        (by sep_focus) ?_
      simp only [RustCliAllocBudget.repAlloc_live_norm, sepConj_assoc]
      let evs_d1 : List AllocEvent :=
        if x.pqCap = 0#64 then [] else rustDeallocEvents x.pqCap.toNat 1
      let st6 := M.stepEvents evs_d1 st5
      refine join_focus_state
        (fun s7 => s7.pc = (blkPl_428).base + bv% (392) ∧ s7.status = .Running ∧ s7.sp = s0.sp - 640#64 ∧
          CalleeSavedPreserved s6 s7 ∧ LsCallInv lsmpl s7 ∧ s7.trace = s0.trace)
        (stackAt (s0.sp - 640#64) (rootStack - 640) ∗
          memRegion (s0.sp - 552#64) 144 ∗
          ((s0.sp - 408#64) ↦₆₄ ck0) ∗ ((s0.sp - 400#64) ↦₆₄ ck1) ∗
          ((s0.sp - 392#64) ↦₆₄ ck2) ∗ ((s0.sp - 384#64) ↦₆₄ ck3) ∗
          ((s0.sp - 376#64) ↦₃₂ ck'.index) ∗ memRegion (s0.sp - 372#64) 116 ∗
          (x.o ↦₆₄ x.pqCap) ∗ ((x.o + 8#64) ↦₆₄ x.pqPtr) ∗
          ((x.o + 152#64) ↦₆₄ ock0) ∗ ((x.o + 160#64) ↦₆₄ ock1) ∗
          ((x.o + 168#64) ↦₆₄ ock2) ∗ ((x.o + 176#64) ↦₆₄ ock3) ∗
          ((x.o + 184#64) ↦₃₂ x.ot.senderChainKey.index) ∗
          (if x.pqCap = 0 then emp else A.live x.pqPtr x.pqCap.toNat 1 ∗ memRegion x.pqPtr x.pqCap.toNat) ∗
          A.pool lim st5 s6)
        (fun s7 =>
          stackAt (s0.sp - 640#64) (rootStack - 640) ∗
            memRegion (s0.sp - 552#64) 296 ∗
            (x.o ↦₆₄ x.pqCap) ∗ ((x.o + 8#64) ↦₆₄ x.pqPtr) ∗
            ((x.o + 152#64) ↦ₛ chainKeyBytes ck') ∗
            A.pool lim st6 s7)
        (by sep_focus)
        (fun R1 hjoin1 => by
          by_cases hpqCap : x.pqCap = 0
          · have hpqCap_beq : (x.pqCap == 0#64) = true := by simp [hpqCap]
            have hst6 : st6 = st5 := by simp [st6, evs_d1, hpqCap]
            have hite : (if x.pqCap = 0 then emp else A.live x.pqPtr x.pqCap.toNat 1 ∗ memRegion x.pqPtr x.pqCap.toNat) = emp := by
              simp only [hpqCap, ↓reduceIte]
            rw [hite]
            simp only [emp_sepConj, sepConj_assoc]
            apply of_sepWP_lsCallInv hinv12 (mid := (blkPl_428).base + bv% (392))
            sync_seg_428 H, ((blkPl_428).base + bv% (392)), hrun6
            rw [← hst6]
            refine SepWP.fold (post_dealloc1_copy_fold x.o s0.sp ck' ck0 ck1 ck2 ck3 hck) (by sep_focus) ?_
            apply SepWP.done
              (by simp (config := { decide := true }) only [arm64_norm])
              (by simp (config := { decide := true }) only [arm64_norm, hrun6])
            intro hinv13
            refine SepWPp.fold (Entails.refl _) (by sep_focus)
              (hjoin1 _ ⟨by simp (config := { decide := true }) only [arm64_norm],
                by simp (config := { decide := true }) only [arm64_norm, hrun6],
                by simp (config := { decide := true }) only [arm64_norm, hsp6],
                ?_, hinv13,
                by simp (config := { decide := true }) only [arm64_norm, htr6]⟩)
            simp only [CalleeSavedPreserved]
            simp (config := { decide := true }) only [arm64_norm]
          · have hpqCap_beq : (x.pqCap == 0#64) = false := bv_beq_false_of_ne hpqCap
            have hst6 : M.stepEvents (rustDeallocEvents x.pqCap.toNat 1) st5 = st6 := by
              simp [st6, evs_d1, show x.pqCap ≠ 0#64 from hpqCap]
            have hite : (if x.pqCap = 0 then emp else A.live x.pqPtr x.pqCap.toNat 1 ∗ memRegion x.pqPtr x.pqCap.toNat) =
                (A.live x.pqPtr x.pqCap.toNat 1 ∗ memRegion x.pqPtr x.pqCap.toNat) := by
              simp only [hpqCap, ↓reduceIte]
            rw [hite]
            simp only [sepConj_assoc]
            apply of_sepWP_lsCallInv hinv12 (mid := lsρ lsRustDeallocSym)
            wp_simp_pre only [stackAt_sub (s0.sp - 640#64) (rootStack - 640) allocHookStack, sepConj_assoc]
            sync_seg_428 H, (lsρ lsRustDeallocSym), hrun6
            refine SepWP.fold (post_dealloc1_copy_fold x.o s0.sp ck' ck0 ck1 ck2 ck3 hck) (by sep_focus) ?_
            apply SepWP.done
              (by simp (config := { decide := true }) only [arm64_norm])
              (by simp (config := { decide := true }) only [arm64_norm, hrun6])
            intro hinv13
            refine call_frame_lsInv
              (x := (x.pqPtr, x.pqCap.toNat, 1, st5))
              hDealloc hinv13
              (by simp (config := { decide := true }) only [arm64_norm])
              (by simp (config := { decide := true }) only [arm64_norm, hrun6])
              (by simp (config := { decide := true }) only [State.spAligned, arm64_norm, hsp_align, hsp6, hsp640_beq])
              rfl rfl
              ⟨by simp (config := { decide := true }) only [arm64_norm],
                by simp (config := { decide := true }) only [arm64_norm],
                by simp (config := { decide := true }) only [arm64_norm],
                by simp (config := { decide := true }) only [wp_norm, arm64_norm]⟩
              (by simp (config := { decide := true }) only [State.sp_writeReg64, State.sp_writeVReg128, State.sp_setPC, State.sp_setPState, State.sp_setMem, ite_true, ite_false, hsp6]; sep_focus)
              (fun _ _ _ _ => allowPanic_not_exited)
              (fun sf _ hm => by
                simp only [sepConj_assoc, satisfies_pure_sepConj] at hm
                exact hm.1.elim)
              fun s7 hpc7 hrun7 hsp7 hcs7 hinv14 => ?_
            simp (config := { decide := true }) only [arm64_norm, hsp6, hst6] at hpc7 hsp7 ⊢
            refine SepWPp.pure_elim fun ⟨hacp7, _⟩ => ?_
            have htr7 : s7.trace = s0.trace := hacp7.2.1.trans htr6
            refine SepWPp.fold
              (Entails.of_eq (stackAt_sub (s0.sp - 640#64) (rootStack - 640) allocHookStack).symm)
              (by sep_focus) ?_
            refine SepWPp.fold (Entails.refl _) (by sep_focus)
              (hjoin1 s7 ⟨hpc7, hrun7, hsp7, ?_, hinv14, htr7⟩)
            simp only [CalleeSavedPreserved] at hcs7 ⊢
            simp (config := { decide := true }) only [arm64_norm, h19_6, h20_6, h21_6, h22_6, h23_6, h24_6, h25_6, h26_6, h27_6, h28_6, h29_6] at hcs7 ⊢
            exact hcs7)
        fun s7 ⟨hpc7, hrun7, hsp7, hcs7, hinv13, htr7⟩ => ?_
      simp only [CalleeSavedPreserved] at hcs7
      simp (config := { decide := true }) only [arm64_norm, h19_6, h20_6, h21_6, h22_6, h23_6, h24_6, h25_6, h26_6, h27_6, h28_6, h29_6] at hcs7
      obtain ⟨h19_7, h20_7, h21_7, h22_7, h23_7, h24_7, h25_7, h26_7, h27_7, h28_7, h29_7⟩ := hcs7
      have hsp7_align : s7.spAligned = true := by simp [State.spAligned, hsp7, hsp640]
      refine SepWPp.fold (vecU8Spare_dealloc A.repAlloc ctCap ctPtr ctext) (by sep_focus) ?_
      simp only [RustCliAllocBudget.repAlloc_live_norm, sepConj_assoc]
      refine SepWPp.pure_elim fun _ => ?_
      refine SepWPp.fold (vecU8Spare_dealloc A.repAlloc pqrMsgCap pqrMsgPtr pqrMsg) (by sep_focus) ?_
      simp only [RustCliAllocBudget.repAlloc_live_norm, sepConj_assoc]
      refine SepWPp.pure_elim fun _ => ?_
      apply of_sepWP_lsCallInv hinv13 (mid := (blkPl_428).base + bv% (456))
      refine SepWP.fold (Entails.of_eq (ret120_split_ok x.ret)) (by sep_focus) ?_
      wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWP.exists_elim fun r14 => SepWP.exists_elim fun r13 =>
        SepWP.exists_elim fun r12 => SepWP.exists_elim fun r11 =>
        SepWP.exists_elim fun r10 => SepWP.exists_elim fun r9 =>
        SepWP.exists_elim fun r8 => SepWP.exists_elim fun r7 =>
        SepWP.exists_elim fun r6 => SepWP.exists_elim fun r5 =>
        SepWP.exists_elim fun r4 => SepWP.exists_elim fun r3 =>
        SepWP.exists_elim fun r2 => SepWP.exists_elim fun r1 =>
        SepWP.exists_elim fun r0 => ?_
      sync_seg_428 H, ((blkPl_428).base + bv% (456)), hrun7
      refine SepWP.fold (msgResultAt_ok_pack A.repAlloc msgG x.ret msg m7 m8 m9 m10 m11 m12 m14) (by sep_focus) ?_
      refine SepWP.fold (otrAt_updated_pack A.repAlloc x.o newPqrCap newPqrPtr x.ot ck' newPqrState) (by sep_focus) ?_
      refine SepWP.fold (post_copy_stack_fold s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
      apply SepWP.done
        (by simp (config := { decide := true }) only [arm64_norm])
        (by simp (config := { decide := true }) only [arm64_norm, hrun7])
      intro hinv14
      let evs_d2 : List AllocEvent :=
        if ctCap = 0#64 then [] else rustDeallocEvents ctCap.toNat 1
      let st7 := M.stepEvents evs_d2 st6
      refine join_focus_state
        (fun s8 => s8.pc = (blkPl_428).base + bv% (480) ∧ s8.status = .Running ∧ s8.sp = s0.sp - 640#64 ∧
          s8.readReg64 (Reg.gpr 1#5) = pqrMsgCap ∧
          CalleeSavedPreserved s7 s8 ∧ LsCallInv lsmpl s8 ∧ s8.trace = s0.trace)
        (stackAt (s0.sp - 640#64) (rootStack - 640) ∗
          ((s0.sp - 576#64) ↦₆₄ newPqrCap) ∗ ((s0.sp - 568#64) ↦₆₄ pqrMsgCap) ∗
          (if ctCap = 0 then emp else A.live ctPtr ctCap.toNat 1 ∗ memRegion ctPtr ctCap.toNat) ∗
          A.pool lim st6 _)
        (fun s8 =>
          stackAt (s0.sp - 640#64) (rootStack - 640) ∗
            memRegion (s0.sp - 576#64) 16 ∗
            A.pool lim st7 s8)
        (by sep_focus)
        (fun R2 hjoin2 => by
          by_cases hctCap : ctCap = 0
          · have hctCap_beq : (ctCap == 0#64) = true := by simp [hctCap]
            have hst7 : st7 = st6 := by simp [st7, evs_d2, hctCap]
            have hite : (if ctCap = 0 then emp else A.live ctPtr ctCap.toNat 1 ∗ memRegion ctPtr ctCap.toNat) = emp := by
              simp only [hctCap, ↓reduceIte]
            rw [hite]
            simp only [emp_sepConj, sepConj_assoc]
            apply of_sepWP_lsCallInv hinv14 (mid := (blkPl_428).base + bv% (480))
            sync_seg_428 H, ((blkPl_428).base + bv% (480)), hrun7
            rw [← hst7]
            refine SepWP.fold (pair_576_entails_memRegion s0.sp _ _) (by sep_focus) ?_
            apply SepWP.done
              (by simp (config := { decide := true }) only [arm64_norm])
              (by simp (config := { decide := true }) only [arm64_norm, hrun7])
            intro hinv15
            refine SepWPp.fold (Entails.refl _) (by sep_focus)
              (hjoin2 _ ⟨by simp (config := { decide := true }) only [arm64_norm],
                by simp (config := { decide := true }) only [arm64_norm, hrun7],
                by simp (config := { decide := true }) only [arm64_norm, hsp7],
                by simp (config := { decide := true }) only [arm64_norm],
                ?_, hinv15,
                by simp (config := { decide := true }) only [arm64_norm, htr7]⟩)
            simp only [CalleeSavedPreserved]
            simp (config := { decide := true }) only [arm64_norm]
          · have hctCap_beq : (ctCap == 0#64) = false := bv_beq_false_of_ne hctCap
            have hst7 : M.stepEvents (rustDeallocEvents ctCap.toNat 1) st6 = st7 := by
              simp [st7, evs_d2, show ctCap ≠ 0#64 from hctCap]
            have hite : (if ctCap = 0 then emp else A.live ctPtr ctCap.toNat 1 ∗ memRegion ctPtr ctCap.toNat) =
                (A.live ctPtr ctCap.toNat 1 ∗ memRegion ctPtr ctCap.toNat) := by
              simp only [hctCap, ↓reduceIte]
            rw [hite]
            simp only [sepConj_assoc]
            apply of_sepWP_lsCallInv hinv14 (mid := lsρ lsRustDeallocSym)
            wp_simp_pre only [stackAt_sub (s0.sp - 640#64) (rootStack - 640) allocHookStack, sepConj_assoc]
            sync_seg_428 H, (lsρ lsRustDeallocSym), hrun7
            apply SepWP.done
              (by simp (config := { decide := true }) only [arm64_norm])
              (by simp (config := { decide := true }) only [arm64_norm, hrun7])
            intro hinv15
            refine call_frame_lsInv
              (x := (ctPtr, ctCap.toNat, 1, st6))
              hDealloc hinv15
              (by simp (config := { decide := true }) only [arm64_norm])
              (by simp (config := { decide := true }) only [arm64_norm, hrun7])
              (by simp (config := { decide := true }) only [State.spAligned, arm64_norm, hsp7_align, hsp_align, hsp7, hsp640_beq])
              rfl rfl
              ⟨by simp (config := { decide := true }) only [arm64_norm, h26_7],
                by simp (config := { decide := true }) only [arm64_norm, h25_7],
                by simp (config := { decide := true }) only [arm64_norm],
                by simp (config := { decide := true }) only [wp_norm, arm64_norm]⟩
              (by simp (config := { decide := true }) only [State.sp_writeReg64, State.sp_writeVReg128, State.sp_setPC, State.sp_setPState, State.sp_setMem, ite_true, ite_false, hsp7]; sep_focus)
              (fun _ _ _ _ => allowPanic_not_exited)
              (fun sf _ hm => by
                simp only [sepConj_assoc, satisfies_pure_sepConj] at hm
                exact hm.1.elim)
              fun s8a hpc8a hrun8a hsp8a hcs8a hinv16 => ?_
            simp only [CalleeSavedPreserved] at hcs8a
            simp (config := { decide := true }) only [arm64_norm, hsp7, h19_7, h20_7, h21_7, h22_7, h23_7, h24_7, h25_7, h26_7, h27_7, h28_7, h29_7] at hpc8a hsp8a hcs8a
            obtain ⟨h19_8a, h20_8a, h21_8a, h22_8a, h23_8a, h24_8a, h25_8a, h26_8a, h27_8a, h28_8a, h29_8a⟩ := hcs8a
            simp (config := { decide := true }) only [arm64_norm, hsp7, hst7]
            refine SepWPp.pure_elim fun ⟨hacp8a, _⟩ => ?_
            have htr8a : s8a.trace = s0.trace := by
              have h1 := hacp8a.2.1
              simpa (config := { decide := true }) only [arm64_norm, htr7] using h1
            refine SepWPp.fold
              (Entails.of_eq (stackAt_sub (s0.sp - 640#64) (rootStack - 640) allocHookStack).symm)
              (by sep_focus) ?_
            apply of_sepWP_lsCallInv hinv16 (mid := (blkPl_428).base + bv% (480))
            sync_seg_428 H, ((blkPl_428).base + bv% (480)), hrun8a
            refine SepWP.fold (pair_576_entails_memRegion s0.sp _ _) (by sep_focus) ?_
            apply SepWP.done
              (by simp (config := { decide := true }) only [arm64_norm])
              (by simp (config := { decide := true }) only [arm64_norm, hrun8a])
            intro hinv17
            refine SepWPp.fold (Entails.refl _) (by sep_focus)
              (hjoin2 _ ⟨by simp (config := { decide := true }) only [arm64_norm],
                by simp (config := { decide := true }) only [arm64_norm, hrun8a],
                by simp (config := { decide := true }) only [arm64_norm, hsp8a],
                by simp (config := { decide := true }) only [arm64_norm],
                ?_, hinv17,
                by simp (config := { decide := true }) only [arm64_norm, htr8a]⟩)
            simp only [CalleeSavedPreserved]
            simp (config := { decide := true }) only [arm64_norm, h19_8a, h20_8a, h21_8a, h22_8a, h23_8a, h24_8a, h25_8a, h26_8a, h27_8a, h28_8a, h29_8a,
              h19_7, h20_7, h21_7, h22_7, h23_7, h24_7, h25_7, h26_7, h27_7, h28_7, h29_7])
        fun s8 ⟨hpc8, hrun8, hsp8, hx1_8, hcs8, hinv15, htr8⟩ => ?_
      simp only [CalleeSavedPreserved] at hcs8
      simp (config := { decide := true }) only [arm64_norm, h19_7, h20_7, h21_7, h22_7, h23_7, h24_7, h25_7, h26_7, h27_7, h28_7, h29_7] at hcs8
      obtain ⟨h19_8, h20_8, h21_8, h22_8, h23_8, h24_8, h25_8, h26_8, h27_8, h28_8, h29_8⟩ := hcs8
      have hsp8_align : s8.spAligned = true := by simp [State.spAligned, hsp8, hsp640]
      let evs_d3 : List AllocEvent :=
        if pqrMsgCap = 0#64 then [] else rustDeallocEvents pqrMsgCap.toNat 1
      let st8 := M.stepEvents evs_d3 st7
      refine join_focus_state
        (fun s9 => s9.pc = (blkPl_428).base + bv% (832) ∧ s9.status = .Running ∧ s9.sp = s0.sp - 640#64 ∧
          CalleeSavedPreserved s8 s9 ∧ LsCallInv lsmpl s9 ∧ s9.trace = s0.trace)
        (stackAt (s0.sp - 640#64) (rootStack - 640) ∗
          (if pqrMsgCap = 0 then emp else A.live pqrMsgPtr pqrMsgCap.toNat 1 ∗ memRegion pqrMsgPtr pqrMsgCap.toNat) ∗
          A.pool lim st7 s8)
        (fun s9 =>
          stackAt (s0.sp - 640#64) (rootStack - 640) ∗
            A.pool lim st8 s9)
        (by sep_focus)
        (fun R3 hjoin3 => by
          by_cases hpqrMsgCap : pqrMsgCap = 0
          · have hpqrMsgCap_beq : (pqrMsgCap == 0#64) = true := by simp [hpqrMsgCap]
            have hst8 : st8 = st7 := by simp [st8, evs_d3, hpqrMsgCap]
            have hite : (if pqrMsgCap = 0 then emp else A.live pqrMsgPtr pqrMsgCap.toNat 1 ∗ memRegion pqrMsgPtr pqrMsgCap.toNat) = emp := by
              simp only [hpqrMsgCap, ↓reduceIte]
            rw [hite]
            simp only [emp_sepConj, sepConj_assoc]
            apply of_sepWP_lsCallInv hinv15 (mid := (blkPl_428).base + bv% (832))
            sync_seg_428 H, ((blkPl_428).base + bv% (832)), hrun8
            rw [← hst8]
            apply SepWP.done
              (by simp (config := { decide := true }) only [arm64_norm])
              (by simp (config := { decide := true }) only [arm64_norm, hrun8])
            intro hinv16
            refine SepWPp.fold (Entails.refl _) (by sep_focus)
              (hjoin3 _ ⟨by simp (config := { decide := true }) only [arm64_norm],
                by simp (config := { decide := true }) only [arm64_norm, hrun8],
                by simp (config := { decide := true }) only [arm64_norm, hsp8],
                ?_, hinv16,
                by simp (config := { decide := true }) only [arm64_norm, htr8]⟩)
            simp only [CalleeSavedPreserved]
            simp (config := { decide := true }) only [arm64_norm]
          · have hpqrMsgCap_beq : (pqrMsgCap == 0#64) = false := bv_beq_false_of_ne hpqrMsgCap
            have hst8 : M.stepEvents (rustDeallocEvents pqrMsgCap.toNat 1) st7 = st8 := by
              simp [st8, evs_d3, show pqrMsgCap ≠ 0#64 from hpqrMsgCap]
            have hite : (if pqrMsgCap = 0 then emp else A.live pqrMsgPtr pqrMsgCap.toNat 1 ∗ memRegion pqrMsgPtr pqrMsgCap.toNat) =
                (A.live pqrMsgPtr pqrMsgCap.toNat 1 ∗ memRegion pqrMsgPtr pqrMsgCap.toNat) := by
              simp only [hpqrMsgCap, ↓reduceIte]
            rw [hite]
            simp only [sepConj_assoc]
            apply of_sepWP_lsCallInv hinv15 (mid := lsρ lsRustDeallocSym)
            wp_simp_pre only [stackAt_sub (s0.sp - 640#64) (rootStack - 640) allocHookStack, sepConj_assoc]
            sync_seg_428 H, (lsρ lsRustDeallocSym), hrun8
            apply SepWP.done
              (by simp (config := { decide := true }) only [arm64_norm])
              (by simp (config := { decide := true }) only [arm64_norm, hrun8])
            intro hinv16
            refine call_frame_lsInv
              (x := (pqrMsgPtr, pqrMsgCap.toNat, 1, st7))
              hDealloc hinv16
              (by simp (config := { decide := true }) only [arm64_norm])
              (by simp (config := { decide := true }) only [arm64_norm, hrun8])
              (by simp (config := { decide := true }) only [State.spAligned, arm64_norm, hsp8_align, hsp_align, hsp8, hsp640_beq])
              rfl rfl
              ⟨by simp (config := { decide := true }) only [arm64_norm, h21_8],
                by simp (config := { decide := true }) only [arm64_norm, hx1_8],
                by simp (config := { decide := true }) only [arm64_norm],
                by simp (config := { decide := true }) only [wp_norm, arm64_norm]⟩
              (by simp (config := { decide := true }) only [State.sp_writeReg64, State.sp_writeVReg128, State.sp_setPC, State.sp_setPState, State.sp_setMem, ite_true, ite_false, hsp8]; sep_focus)
              (fun _ _ _ _ => allowPanic_not_exited)
              (fun sf _ hm => by
                simp only [sepConj_assoc, satisfies_pure_sepConj] at hm
                exact hm.1.elim)
              fun s9 hpc9 hrun9 hsp9 hcs9 hinv17 => ?_
            simp (config := { decide := true }) only [arm64_norm, hsp8, hst8] at hpc9 hsp9 ⊢
            refine SepWPp.pure_elim fun ⟨hacp9, _⟩ => ?_
            have htr9 : s9.trace = s0.trace := hacp9.2.1.trans htr8
            refine SepWPp.fold
              (Entails.of_eq (stackAt_sub (s0.sp - 640#64) (rootStack - 640) allocHookStack).symm)
              (by sep_focus) ?_
            refine SepWPp.fold (Entails.refl _) (by sep_focus)
              (hjoin3 s9 ⟨hpc9, hrun9, hsp9, ?_, hinv17, htr9⟩)
            simp only [CalleeSavedPreserved] at hcs9 ⊢
            simp (config := { decide := true }) only [arm64_norm, h19_8, h20_8, h21_8, h22_8, h23_8, h24_8, h25_8, h26_8, h27_8, h28_8, h29_8] at hcs9 ⊢
            exact hcs9)
        fun s9 ⟨hpc9, hrun9, hsp9, hcs9, _, htr9⟩ => ?_
      simp only [CalleeSavedPreserved] at hcs9
      simp (config := { decide := true }) only [arm64_norm, h19_8, h20_8, h21_8, h22_8, h23_8, h24_8, h25_8, h26_8, h27_8, h28_8, h29_8] at hcs9
      obtain ⟨h19_9, h20_9, h21_9, h22_9, h23_9, h24_9, h25_9, h26_9, h27_9, h28_9, h29_9⟩ := hcs9
      apply SepWPp.of_sepWP_ret
      sync_seg_428 H, (s0.readReg64 Reg.lr), hrun9
      refine SepWP.fold (ok_branch_epilogue_stack s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
      let evs_tot := evs_spqr ++ evs_mk ++ evs_gk ++ evs_aes ++ evs_new ++ evs_d1 ++ evs_d2 ++ evs_d3
      have hst_some : st8 = M.stepEvents evs_tot st0 := by
        simp only [st8, st7, st6, st5, st4, st3, st2, st1, evs_tot, M.stepEvents_append]
      rw [hst_some]
      have hev_some : OtrEncryptStepEnv C S uuidTryParse SendEnv FmtEnv x evs_tot := by
        have haes_eq : evs_aes = rustAllocEvents ((x.ptext.length / 16 + 1) * 16) 1 := hev_aes
        simp only [OtrEncryptStepEnv, hsend]
        refine ⟨evs_spqr, evs_mk, evs_gk, evs_d2, evs_d3,
          hev_spqr, hev_mk, hev_gk,
          optVecDropEnv_of_cap ctext.length ctCap hctLenLeCap hctCapLt,
          optVecDropEnv_of_cap pqrMsg.length pqrMsgCap hpqrMsgLenLeCap hpqrMsgCapLt, ?_⟩
        simp only [evs_tot, haes_eq, evs_new, evs_d1, List.append_assoc]
      apply sepWP_done_encrypt_coins_budget
        (by simp (config := { decide := true }) only [arm64_norm, h29_9])
        (by simp (config := { decide := true }) only [arm64_norm, hrun9])
        (model_of_send_some_ok_eq x C S newPqrState pqrKey pqrMsg ck' hnp1 hsend hnck (msg := msg) rfl)
        hev_some
        (by simp)
        (by simp (config := { decide := true }) only [arm64_norm, htr9])
        (by sep_focus)
        (by simp (config := { decide := true }) only [arm64_norm, hsp9, BitVec.sub_add_cancel])
        (by simp only [CalleeSavedPreserved]; simp (config := { decide := true }) only [arm64_norm, h29_9])

end Block428Body

theorem otrEncrypt_coins_placed_step_body_ok [LibsignalPlacement] {M : AllocCostModel}
    (Q : List (BitVec 8) → Prop) (C : Crypto) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (SendEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop :=
      fun _ _ evs => evs = [])
    (FmtEnv : List AllocEvent → Prop := FormatInnerEnv)
    (H : String → Option (State → State))
    (hFmtWit : ∃ evs, FmtEnv evs := by exact ⟨[], rfl⟩)
    (h_aes : HookSat H lsAesEncSym (aesEncBudgetSpec C.E M A lim))
    (h_fmt : HookSat H lsFormatInnerSym (formatInnerBudgetEnvSpec M A lim FmtEnv))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hSend : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 427)
      (withLsCodeRoLoaded lsmpl
        { spqrSendCoinsPlacedSpec M A lim ctl S (fun sc evs => SendEnv sc.st.bytes sc.rest evs) with
          pre := fun (sc, st) s =>
            ⌜Q sc.st.bytes⌝ ∗
              (spqrSendCoinsPlacedSpec M A lim ctl S
                (fun sc evs => SendEnv sc.st.bytes sc.rest evs)).pre (sc, st) s }))
    (hMK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 38) (withLsCodeRoLoaded lsmpl (messageKeysPlacedSpec C.F A lim)))
    (hGK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 69) (withLsCodeRoLoaded lsmpl (generateKeysSpec M A lim C.F)))
    (hNew : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 63) (withLsCodeRoLoaded lsmpl (signalMessageNewSpec M A lim C.F uuidTryParse)))
    (hNCK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 39) (withLsCodeRoLoaded lsmpl (nextChainKeyPlacedSpec C.F))) :
    subroutine_ok ((blkPC_428).rebase (blkPl_428).base H) (blkPl_428).base
      (withLsCodeRoLoaded lsmpl
        { otrEncryptCoinsPlacedStepSpec C A lim ctl uuidTryParse S SendEnv FmtEnv with
          pre := fun (x, st) s =>
            ⌜Q x.ot.pqrState⌝ ∗
              (otrEncryptCoinsPlacedStepSpec C A lim ctl uuidTryParse S SendEnv FmtEnv).pre
                (x, st) s }) := by
  have h := otrEncrypt_coins_placed_step_body_ok_frame (fun st _ => Q st) emp C A lim ctl S
    SendEnv FmtEnv H hFmtWit h_aes h_fmt h_dealloc
    (by simpa only [emp_sepConj] using hSend) hMK hGK hNew hNCK
  simpa only [emp_sepConj] using h

theorem otrEncrypt_coins_placed_env_body_ok_frame [LibsignalPlacement] {M : AllocCostModel}
    (Q : List (BitVec 8) → List (BitVec 8) → Prop) (F : SepProp)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (S : SpqrModel)
    (EncryptEnv : OtrEncryptGhost → List AllocEvent → Prop)
    (SendEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop :=
      fun _ _ evs => evs = [])
    (FmtEnv : List AllocEvent → Prop := FormatInnerEnv)
    (H : String → Option (State → State))
    (hImp : ∀ x evs, Q x.ot.pqrState x.rest → x.ptext.length < 2 ^ 32 →
      OtrEncryptStepEnv C S uuidTryParse SendEnv FmtEnv x evs → EncryptEnv x evs)
    (hFmtWit : ∃ evs, FmtEnv evs := by exact ⟨[], rfl⟩)
    (h_aes : HookSat H lsAesEncSym (aesEncBudgetSpec C.E M A lim))
    (h_fmt : HookSat H lsFormatInnerSym (formatInnerBudgetEnvSpec M A lim FmtEnv))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hSend : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 427)
      (withLsCodeRoLoaded lsmpl
        { spqrSendCoinsPlacedSpec M A lim ctl S (fun sc evs => SendEnv sc.st.bytes sc.rest evs) with
          pre := fun (sc, st) s =>
            ⌜Q sc.st.bytes sc.rest⌝ ∗ F ∗
              (spqrSendCoinsPlacedSpec M A lim ctl S
                (fun sc evs => SendEnv sc.st.bytes sc.rest evs)).pre (sc, st) s
          post := fun (sc, st) s0 sf =>
            F ∗ (spqrSendCoinsPlacedSpec M A lim ctl S
              (fun sc evs => SendEnv sc.st.bytes sc.rest evs)).post (sc, st) s0 sf }))
    (hMK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 38) (withLsCodeRoLoaded lsmpl (messageKeysPlacedSpec C.F A lim)))
    (hGK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 69) (withLsCodeRoLoaded lsmpl (generateKeysSpec M A lim C.F)))
    (hNew : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 63) (withLsCodeRoLoaded lsmpl (signalMessageNewSpec M A lim C.F uuidTryParse)))
    (hNCK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 39) (withLsCodeRoLoaded lsmpl (nextChainKeyPlacedSpec C.F))) :
    subroutine_ok ((blkPC_428).rebase (blkPl_428).base H) (blkPl_428).base
      (withLsCodeRoLoaded lsmpl
        { otrEncryptCoinsPlacedEnvSpec C A lim ctl uuidTryParse S EncryptEnv with
          pre := fun (x, st) s =>
            ⌜Q x.ot.pqrState x.rest⌝ ∗ F ∗
              (otrEncryptCoinsPlacedEnvSpec C A lim ctl uuidTryParse S EncryptEnv).pre (x, st) s
          post := fun (x, st) s0 sf =>
            F ∗ (otrEncryptCoinsPlacedEnvSpec C A lim ctl uuidTryParse S EncryptEnv).post
              (x, st) s0 sf }) :=
  subroutine_ok_otrEncryptCoinsPlacedEnv_framed_of_imp hImp
    (otrEncrypt_coins_placed_step_body_ok_frame Q F C A lim ctl S SendEnv FmtEnv H hFmtWit
      h_aes h_fmt h_dealloc hSend hMK hGK hNew hNCK)

theorem otrEncrypt_coins_placed_env_body_ok [LibsignalPlacement] {M : AllocCostModel}
    (Q : List (BitVec 8) → Prop) (C : Crypto) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (EncryptEnv : OtrEncryptGhost → List AllocEvent → Prop)
    (SendEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop :=
      fun _ _ evs => evs = [])
    (FmtEnv : List AllocEvent → Prop := FormatInnerEnv)
    (H : String → Option (State → State))
    (hImp : ∀ x evs, Q x.ot.pqrState → x.ptext.length < 2 ^ 32 →
      OtrEncryptStepEnv C S uuidTryParse SendEnv FmtEnv x evs → EncryptEnv x evs)
    (hFmtWit : ∃ evs, FmtEnv evs := by exact ⟨[], rfl⟩)
    (h_aes : HookSat H lsAesEncSym (aesEncBudgetSpec C.E M A lim))
    (h_fmt : HookSat H lsFormatInnerSym (formatInnerBudgetEnvSpec M A lim FmtEnv))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hSend : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 427)
      (withLsCodeRoLoaded lsmpl
        { spqrSendCoinsPlacedSpec M A lim ctl S (fun sc evs => SendEnv sc.st.bytes sc.rest evs) with
          pre := fun (sc, st) s =>
            ⌜Q sc.st.bytes⌝ ∗
              (spqrSendCoinsPlacedSpec M A lim ctl S
                (fun sc evs => SendEnv sc.st.bytes sc.rest evs)).pre (sc, st) s }))
    (hMK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 38) (withLsCodeRoLoaded lsmpl (messageKeysPlacedSpec C.F A lim)))
    (hGK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 69) (withLsCodeRoLoaded lsmpl (generateKeysSpec M A lim C.F)))
    (hNew : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 63) (withLsCodeRoLoaded lsmpl (signalMessageNewSpec M A lim C.F uuidTryParse)))
    (hNCK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 39) (withLsCodeRoLoaded lsmpl (nextChainKeyPlacedSpec C.F))) :
    subroutine_ok ((blkPC_428).rebase (blkPl_428).base H) (blkPl_428).base
      (withLsCodeRoLoaded lsmpl
        { otrEncryptCoinsPlacedEnvSpec C A lim ctl uuidTryParse S EncryptEnv with
          pre := fun (x, st) s =>
            ⌜Q x.ot.pqrState⌝ ∗
              (otrEncryptCoinsPlacedEnvSpec C A lim ctl uuidTryParse S EncryptEnv).pre
                (x, st) s }) := by
  have h := otrEncrypt_coins_placed_env_body_ok_frame (fun st _ => Q st) emp C A lim ctl S
    EncryptEnv SendEnv FmtEnv H (fun x evs hQ hpt he => hImp x evs hQ hpt he) hFmtWit
    h_aes h_fmt h_dealloc (by simpa only [emp_sepConj] using hSend) hMK hGK hNew hNCK
  simpa only [emp_sepConj] using h

/-! ## `otrEncryptPlacedSpecQF` and `otrEncryptPlacedSpecQ` Theorems -/

theorem otrEncrypt_coins_placed_body_ok_frame [LibsignalPlacement] {M : AllocCostModel}
    (Q : List (BitVec 8) → List (BitVec 8) → Prop) (F : SepProp)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (S : SpqrModel)
    (SendEnv : SpqrSendBudgetEnv := fun _ _ evs => evs = [])
    (H : String → Option (State → State))
    (h_aes : HookSat H lsAesEncSym (aesEncBudgetSpec C.E M A lim))
    (h_fmt : HookSat H lsFormatInnerSym (formatInnerBudgetEnvSpec M A lim FormatInnerEnv))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hSend : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 427)
      (withLsCodeRoLoaded lsmpl
        { spqrSendCoinsPlacedSpec M A lim ctl S (fun sc evs => SendEnv sc.st.bytes sc.rest evs) with
          pre := fun (sc, st) s =>
            ⌜Q sc.st.bytes sc.rest⌝ ∗ F ∗
              (spqrSendCoinsPlacedSpec M A lim ctl S
                (fun sc evs => SendEnv sc.st.bytes sc.rest evs)).pre (sc, st) s
          post := fun (sc, st) s0 sf =>
            F ∗ (spqrSendCoinsPlacedSpec M A lim ctl S
              (fun sc evs => SendEnv sc.st.bytes sc.rest evs)).post (sc, st) s0 sf }))
    (hMK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 38) (withLsCodeRoLoaded lsmpl (messageKeysPlacedSpec C.F A lim)))
    (hGK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 69) (withLsCodeRoLoaded lsmpl (generateKeysSpec M A lim C.F)))
    (hNew : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 63) (withLsCodeRoLoaded lsmpl (signalMessageNewSpec M A lim C.F uuidTryParse)))
    (hNCK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 39) (withLsCodeRoLoaded lsmpl (nextChainKeyPlacedSpec C.F))) :
    subroutine_ok ((blkPC_428).rebase (blkPl_428).base H) (blkPl_428).base
      (withLsCodeRoLoaded lsmpl
        (otrEncryptPlacedSpecQF Q F C A lim ctl uuidTryParse S SendEnv)) := by
  have hbase := otrEncrypt_coins_placed_env_body_ok_frame Q F C A lim ctl S
    (OtrEncryptEnv C S SendEnv uuidTryParse) SendEnv FormatInnerEnv H
    (fun _ _ _ _ he => otrEncryptEnv_of_stepEnv he) ⟨[], rfl⟩
    h_aes h_fmt h_dealloc hSend hMK hGK hNew hNCK
  refine subroutine_ok_mono hbase
    (fun ⟨x, st⟩ R s0 hp => ?_)
    (fun ⟨x, st⟩ R s0 sf hq => ?_)
  · dsimp only [withLsCodeRoLoaded, otrEncryptPlacedSpecQF, otrEncryptPlacedSpec,
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptPlacedSpecQF,
      otrEncryptCoinsPlacedEnvSpec] at hp ⊢
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hp
  · dsimp only [withLsCodeRoLoaded, otrEncryptPlacedSpecQF, otrEncryptPlacedSpec,
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptPlacedSpecQF,
      otrEncryptCoinsPlacedEnvSpec] at hq ⊢
    have hq1 : sf.mem ⊨
        (∃∗ evs : List AllocEvent,
          ⌜OtrEncryptEnv C S SendEnv uuidTryParse x evs⌝ ∗
          (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptPlacedSpec C
            (A.atState lim (M.stepEvents evs st) sf) ctl uuidTryParse S).post x s0 sf) ∗
        (F ∗ R) :=
      Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hq
    rw [sepExists_sepConj_left, satisfies_sepExists] at hq1
    obtain ⟨evs, hevs⟩ := hq1
    rw [sepExists_sepConj_left, satisfies_sepExists]
    exact ⟨evs, Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hevs⟩

theorem otrEncrypt_coins_placed_body_ok [LibsignalPlacement] {M : AllocCostModel}
    (Q : List (BitVec 8) → Prop) (C : Crypto) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ctl : BitVec 64) (S : SpqrModel)
    (SendEnv : SpqrSendBudgetEnv := fun _ _ evs => evs = [])
    (H : String → Option (State → State))
    (h_aes : HookSat H lsAesEncSym (aesEncBudgetSpec C.E M A lim))
    (h_fmt : HookSat H lsFormatInnerSym (formatInnerBudgetEnvSpec M A lim FormatInnerEnv))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hSend : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 427)
      (withLsCodeRoLoaded lsmpl
        { spqrSendCoinsPlacedSpec M A lim ctl S (fun sc evs => SendEnv sc.st.bytes sc.rest evs) with
          pre := fun (sc, st) s =>
            ⌜Q sc.st.bytes⌝ ∗
              (spqrSendCoinsPlacedSpec M A lim ctl S
                (fun sc evs => SendEnv sc.st.bytes sc.rest evs)).pre (sc, st) s }))
    (hMK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 38) (withLsCodeRoLoaded lsmpl (messageKeysPlacedSpec C.F A lim)))
    (hGK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 69) (withLsCodeRoLoaded lsmpl (generateKeysSpec M A lim C.F)))
    (hNew : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 63) (withLsCodeRoLoaded lsmpl (signalMessageNewSpec M A lim C.F uuidTryParse)))
    (hNCK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 39) (withLsCodeRoLoaded lsmpl (nextChainKeyPlacedSpec C.F))) :
    subroutine_ok ((blkPC_428).rebase (blkPl_428).base H) (blkPl_428).base
      (withLsCodeRoLoaded lsmpl
        (otrEncryptPlacedSpecQ Q C A lim ctl uuidTryParse S SendEnv)) := by
  have h := otrEncrypt_coins_placed_body_ok_frame (fun st _ => Q st) emp C A lim ctl S
    SendEnv H h_aes h_fmt h_dealloc
    (by simpa only [emp_sepConj] using hSend) hMK hGK hNew hNCK
  simpa only [otrEncryptPlacedSpecQF, otrEncryptPlacedSpecQ, otrEncryptPlacedSpec,
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptPlacedSpecQF,
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptPlacedSpecQ,
    emp_sepConj] using h

end LibsignalBinary.Proofs.Cli.TripleRatchet.Encrypt.CorePlacedBudget

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.Branches
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.RecordCodecs.RoundTrip
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.Fetches
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Store.IdSavePoll.Helpers

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli

private theorem ispoll_onPanic {img : Obj.Image} {A : RustAlloc}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {stk : Nat}
    {x : IdPollGhost} {s0 sf : State} {P_f : SepProp}
    (hp : allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) :
    P_f ⊢ (idSavePollSpec rd pathOk A img stk).onPanic x s0 sf := by
  simp only [idSavePollSpec, Spec.inImage]
  exact Entails.pure_right hp (entails_anyHeap _)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm] calleeSavedVRegs_writeVReg128_0

private theorem pk_hh16 (h1 : BitVec 16) (b2 : BitVec 8) :
    (h1.zeroExtend 64 ||| (b2.zeroExtend 32 <<< 16).zeroExtend 64).truncate 32 =
      h1.zeroExtend 32 ||| (b2.zeroExtend 32 <<< 16) := by
  ext i hi; interval_cases i <;> simp

private theorem bv_shr32_tr32_tr16 (v : BitVec 64) :
    ((v >>> 32).truncate 32).truncate 16 = (v >>> 32).truncate 16 := by
  ext i hi; interval_cases i <;> simp

private theorem abstract_state {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (k : ∀ s' : State, s' = s → SepWPp prog ret s' P Q Qp) :
    SepWPp prog ret s P Q Qp :=
  k s rfl

/-- Continuation of `ispoll_branch_ok_some` from `+220` (`offAfterDealloc`) through
`<PublicKey as PartialEq>::eq` (at parametric `eqStk ≤ saveSubMax getStk putStk`) into
`ispoll_ok_tail_190`. -/
private theorem ispoll_branch_ok_some_220_gen {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {getStk putStk eqStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hPut : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutStrName)
      (dirPutStrSpec A img putStk))
    (hEq' : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idSavePollName +
        bv% (2 ^ 64 + ls_off% "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" -
          ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))
      (publicKeyEqAtSpec eqStk))
    (heq_le : eqStk ≤ saveSubMax getStk putStk)
    (hstk : saveMinStk getStk putStk ≤ stk)
    (hhi : stk ≤ 2 ^ 64)
    {s0 s : State} (x : IdPollGhost) (k : IdentityKey)
    (c1 c2 c3 c4 c5 c6 c7 c15 : BitVec 8)
    (s16 : BitVec 64) (s24 : BitVec 8) (s32 : BitVec 64) (s40 : BitVec 8)
    (s56w : BitVec 64)
    (w0 : BitVec 32) (h1 : BitVec 16) (b2 : BitVec 8) (d3 d4 d5 : BitVec 64) (b6 : BitVec 8)
    (hpk_eq : ∀ a : BitVec 64, (a ↦ₛ k.publicKey.bytes.toList) = pkChunksAt a w0 h1 b2 d3 d4 d5 b6)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr idSavePollName + offAfterDealloc)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0xd0#64)
    (hsp_align : s.spAligned = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace)
    (hinv : ImgCallInv img s)
    (hx19 : s.readReg64 .x19 = x.call.fut)
    (hx20 : s.readReg64 .x20 = x.call.out)
    (hx22 : s.readReg64 .x22 = d4)
    (hx24 : s.readReg64 .x24 = x.self)
    (hx25 : s.readReg64 .x25 = okTagVec)
    (hx26 : s.readReg64 .x26 = 1#64)
    (hx27 : s.readReg64 .x27 =
      w0.zeroExtend 64 ||| ((h1.zeroExtend 64 ||| (b2.zeroExtend 32 <<< 16).zeroExtend 64).truncate 32).zeroExtend 64 <<< 32)
    (hx28 : s.readReg64 .x28 = d3)
    (hx29 : s.readReg64 .x29 = s0.sp - 0x60#64)
    (hnlen : x.call.call.addr.name.bytes.length < 2 ^ 32)
    (hclen : x.peers.changed.length < 2 ^ 32)
    (hgr : Except.ok k.serialize = x.peers.get rd s0.fs.files x.call.call.addr.val.name)
    (hans : IdPeerAns (.ok k.serialize) (.ok (some k))) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s
      (stackAt (s0.sp - 0xd0#64) (saveSubMax getStk putStk) ∗
        memRegion (s0.sp - 0x90#64) 32 ∗
        memRegion (s0.sp - 0x70#64) 16 ∗
        A.pool ∗
        ((s0.sp - 0xa0#64) ↦₆₄ d5) ∗
        ((s0.sp - 0x98#64) ↦₈ b6) ∗
        overlap7View1 (s0.sp - 0x97#64)
          (s56w.extractLsb' 8 8) (s56w.extractLsb' 16 8) (s56w.extractLsb' 24 8)
          (s56w.extractLsb' 32 8) (s56w.extractLsb' 40 8) (s56w.extractLsb' 48 8) (s56w.extractLsb' 56 8) ∗
        logOff img ∗
        dirAt A (x.self + 0x28#64) x.peers ∗
        memRegion x.call.out 48 ∗
        idSaveBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 0#8 ∗
        protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
        (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - saveMinStk getStk putStk) ∗
        memRegion (s0.sp - 0xd0#64) 8 ∗
        overlap7View1 (s0.sp - 0xc8#64) c1 c2 c3 c4 c5 c6 c7 ∗
        ((s0.sp - 0xc1#64) ↦₈ c15) ∗
        ((s0.sp - 0xc0#64) ↦₆₄ s16) ∗
        ((s0.sp - 0xb8#64) ↦₈ s24) ∗
        memRegion (s0.sp - 0xb7#64) 7 ∗
        ((s0.sp - 0xb0#64) ↦₆₄ s32) ∗
        ((s0.sp - 0xa8#64) ↦₈ s40) ∗
        memRegion (s0.sp - 0xa7#64) 7 ∗
        savedCalleeSlots s0)
      (fun sf P_f => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (idSavePollSpec rd pathOk A img stk).post x s0 sf))
      (fun sf P_f => P_f ⊢ (idSavePollSpec rd pathOk A img stk).onPanic x s0 sf) := by
  have hsub_hi : saveSubMax getStk putStk ≤ 2 ^ 64 := by
    have : saveMinStk getStk putStk ≤ 2 ^ 64 := le_trans hstk hhi
    unfold saveMinStk at this; omega
  have hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) →
      (P_f ⊢ (idSavePollSpec rd pathOk A img stk).onPanic x s0 sf) :=
    fun _ _ hp => ispoll_onPanic hp
  have hfn : libsignalSessionCode.fnOff idSavePollName =
      num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}") :=
    idSavePoll_fnOff
  code_fetches CryptoVerification.libsignalSessionCode cliIdSavePollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}")) 400
  clear hfn
  dsimp only [tripleRatchetProgAtExt, offAfterDealloc] at hEq' hpc ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr idSavePollName = entry
  examples_hide_fetches
  ispoll_rw_pre (memRegion_32_eq_pkChunksAt (s0.sp - 0x90#64))
  conv =>
    arg 4
    unfold pkChunksAt idSaveBoxAt
    simp only [ispoll_sp_eqs, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro u0
  apply SepWPp.exists_elim; intro u1
  apply SepWPp.exists_elim; intro u2
  apply SepWPp.exists_elim; intro u3
  apply SepWPp.exists_elim; intro u4
  apply SepWPp.exists_elim; intro u5
  apply SepWPp.exists_elim; intro u6
  apply sepWPp_step_to_frozen hinv (mid := entry +
    bv% (2 ^ 64 + ls_off% "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" -
      ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF_eq hsym_eq
  have hrew_pk :
      (((s0.sp - 0x90#64) ↦₃₂ (w0.zeroExtend 64 ||| ((h1.zeroExtend 64 ||| (b2.zeroExtend 32 <<< 16).zeroExtend 64).truncate 32).zeroExtend 64 <<< 32).truncate 32) ∗
        ((s0.sp - 0x8c#64) ↦₁₆ ((((w0.zeroExtend 64 ||| ((h1.zeroExtend 64 ||| (b2.zeroExtend 32 <<< 16).zeroExtend 64).truncate 32).zeroExtend 64 <<< 32) >>> 32)).truncate 32).truncate 16) ∗
        ((s0.sp - 0x8a#64) ↦₈ (((w0.zeroExtend 64 ||| ((h1.zeroExtend 64 ||| (b2.zeroExtend 32 <<< 16).zeroExtend 64).truncate 32).zeroExtend 64 <<< 32) >>> 48)).truncate 8) ∗
        ((s0.sp - 0x89#64) ↦₆₄ d3) ∗ ((s0.sp - 0x81#64) ↦₆₄ d4) ∗ ((s0.sp - 0x79#64) ↦₆₄ d5) ∗
        ((s0.sp - 0x71#64) ↦₈ b6)) =
      ((s0.sp - 0x90#64) ↦ₛ k.publicKey.bytes.toList) := by
    rw [pk_hh16 h1 b2, bv_shr32_tr32_tr16, pk_pack_lo32 w0 h1 b2, pk_pack_mid16 w0 h1 b2,
      pk_pack_hi8 w0 h1 b2, hpk_eq (s0.sp - 0x90#64)]
    unfold pkChunksAt
    simp only [ispoll_sp_eqs]
  ispoll_rw_pre hrew_pk
  conv =>
    arg 4
    rw [stackAt_sub_split (s0.sp - 0xd0#64) heq_le hsub_hi]
    simp only [sepConj_assoc]
  refine ispoll_call_publicKeyEq_stk (ret_pc := entry + offAfterEq)
    hEq' (s0.sp - 0x90#64) k.publicKey x.call.call.keyA x.call.call.key.publicKey ?ispollF3
    (by wp_norm_goal) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_goal) (by wp_norm_goal)
    ⟨hF_eq, hsym_eq⟩
    (by wp_norm_goal) (by wp_norm_goal) hpan
    ?ispollPre3 ?_
  case ispollPre3 => ispoll_close_frame
  intro sm3 hpc3 hrun3 hsp3 hcs3 hinv3 hx0_3 htr3
  simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm,
    hsp, htr, hx19, hx20, hx22, hx24, hx25, hx26, hx27, hx28, hx29, hvregs]
    at hpc3 hsp3 htr3 hx0_3 hcs3
  rcases hcs3 with ⟨hx19_3, hx20_3, _, _, _, hx24_3, _, _, _, _, hx29_3, hvregs_3⟩
  have hsp_al3 : sm3.spAligned = true := by
    simp only [State.spAligned] at hsp_align ⊢
    rwa [hsp3, ← hsp]
  conv => arg 4; simp only [State.sp, wp_norm, arm64_norm, hsp, hsp3]
  ispoll_rw_pre (stackAt_sub_split (s0.sp - 0xd0#64) heq_le hsub_hi).symm
  ispoll_fold_pre (slot90_bytes32_16_collapse s0.sp k.publicKey.bytes.toList_length)
  ispoll_fold_pre (s48_byte7_entails_memRegion16 s0.sp d5 b6
    (s56w.extractLsb' 8 8) (s56w.extractLsb' 16 8) (s56w.extractLsb' 24 8)
    (s56w.extractLsb' 32 8) (s56w.extractLsb' 40 8) (s56w.extractLsb' 48 8) (s56w.extractLsb' 56 8))
  apply sepWPp_step_to_frozen hinv3 (mid := entry + offOkTail)
  dsimp only [offOkTail]
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF_tail hsym_tail
  apply abstract_state; intro s4 hs4
  let chg : IdentityChange := if k = x.call.call.key then .newOrUnchanged else .replacedExisting
  have hpc4 : s4.pc = (tripleRatchetProgAtExt img.base ext).fnAddr idSavePollName + offOkTail := by
    rw [hs4]; dsimp only [tripleRatchetProgAtExt]; rw [hentry]; wp_norm_goal
  have hrun4 : s4.status = .Running := by rw [hs4]; wp_norm_lhs
  have hsp4 : s4.sp = s0.sp - 0xd0#64 := by rw [hs4]; wp_norm_goal
  have hsp_al4 : s4.spAligned = true := by rw [hs4]; wp_norm_lhs
  have hvregs4 : calleeSavedVRegs s4 = calleeSavedVRegs s0 := by
    rw [hs4]; simp only [wp_norm, arm64_norm, hvregs_3]
  have htr4 : s4.trace = s0.trace := by rw [hs4]; wp_norm_goal
  have hinv4 : ImgCallInv img s4 := by rw [hs4]; exact ⟨hF_tail, hsym_tail⟩
  have hx19_4 : s4.readReg64 .x19 = x.call.fut := by rw [hs4]; wp_norm_goal
  have hx20_4 : s4.readReg64 .x20 = x.call.out := by rw [hs4]; wp_norm_goal
  have hx24_4 : s4.readReg64 .x24 = x.self := by rw [hs4]; wp_norm_goal
  have hx26_4 : (s4.readReg64 .x26).truncate 32 =
      (if chg == .replacedExisting then 1#32 else 0#32) := by
    have htr_xor : ∀ (P : Prop) [Decidable P],
        BitVec.truncate 32 ((if P then 1#64 else 0#64) ^^^ 4294967297#64) =
          BitVec.truncate 32 (if P then 1#64 else 0#64) ^^^ 1#32 := by
      intro P _; split_ifs <;> rfl
    rw [hs4]; simp only [chg, wp_norm, arm64_norm]
    rw [htr_xor]
    exact eor_publicKey_eq_idSaveOf k x.call.call.key
  have hx29_4 : s4.readReg64 .x29 = s0.sp - 0x60#64 := by rw [hs4]; wp_norm_goal
  have hc4 : idSaveOf (.ok (some k)) x.call.call.key = .ok chg := by
    by_cases h : k = x.call.call.key <;> simp [idSaveOf, chg, h]
  clear hs4 hF_tail hsym_tail
  change SepWPp (tripleRatchetProgAtExt img.base ext) _ _ _ _ _
  refine sepWPp_conseq ?_
    (ispoll_ok_tail_190 (pathOk := pathOk) hC hPut hstk hhi x (.ok k.serialize) (some k) chg
      c1 c2 c3 c4 c5 c6 c7 c15 s16 s24 d5 b6
      hpc4 hrun4 hsp4 hsp_al4 hvregs4 htr4 hinv4
      hx19_4 hx20_4 hx24_4 hx26_4 hx29_4 hc4 hnlen hclen hgr hans)
  exact Entails.of_eq (by unfold idSaveBoxAt; ispoll_ac_rfl)

/-- `Ok k.serialize` branch after `Dir::get` returns at `+68` (`gr = .ok k.serialize`),
parameterized over `eqStk ≤ saveSubMax getStk putStk`. -/
theorem ispoll_branch_ok_some_gen {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {getStk putStk eqStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hPut : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutStrName)
      (dirPutStrSpec A img putStk))
    (hDec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyDecodeName)
      (identityKeyDecodeSpec A img))
    (hEqAt : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idSavePollName +
        bv% (2 ^ 64 + ls_off% "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" -
          ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))
      (publicKeyEqAtSpec eqStk))
    (heq_le : eqStk ≤ saveSubMax getStk putStk)
    (hstk : saveMinStk getStk putStk ≤ stk)
    (hhi : stk ≤ 2 ^ 64)
    {s0 s : State} (x : IdPollGhost) (k : IdentityKey) {bs : List (BitVec 8)}
    (c1 c2 c3 c4 c5 c6 c7 c15 : BitVec 8)
    (s16 : BitVec 64) (s24 : BitVec 8) (s32 : BitVec 64) (s40 : BitVec 8)
    (s48 s56w : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr idSavePollName + offAfterGet)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0xd0#64)
    (hsp_align : s.spAligned = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace)
    (hinv : ImgCallInv img s)
    (hx19 : s.readReg64 .x19 = x.call.fut)
    (hx20 : s.readReg64 .x20 = x.call.out)
    (hx24 : s.readReg64 .x24 = x.self)
    (hx29 : s.readReg64 .x29 = s0.sp - 0x60#64)
    (hnlen : x.call.call.addr.name.bytes.length < 2 ^ 32)
    (hclen : x.peers.changed.length < 2 ^ 32)
    (hser : k.serialize = bs)
    (hgr : Except.ok bs = x.peers.get rd s0.fs.files x.call.call.addr.val.name) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s
      (getResultAt A (s0.sp - 0x90#64) (.ok bs) ∗
        dirAt A (x.self + 0x28#64) x.peers ∗
        memRegion x.call.out 48 ∗
        idSaveBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 0#8 ∗
        protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
        (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗
        logOff img ∗ A.pool ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - saveMinStk getStk putStk) ∗
        stackAt (s0.sp - 0xd0#64) (saveSubMax getStk putStk) ∗
        memRegion (s0.sp - 0xd0#64) 8 ∗
        overlap7View1 (s0.sp - 0xc8#64) c1 c2 c3 c4 c5 c6 c7 ∗
        ((s0.sp - 0xc1#64) ↦₈ c15) ∗
        ((s0.sp - 0xc0#64) ↦₆₄ s16) ∗
        ((s0.sp - 0xb8#64) ↦₈ s24) ∗
        memRegion (s0.sp - 0xb7#64) 7 ∗
        ((s0.sp - 0xb0#64) ↦₆₄ s32) ∗
        ((s0.sp - 0xa8#64) ↦₈ s40) ∗
        memRegion (s0.sp - 0xa7#64) 7 ∗
        ((s0.sp - 0xa0#64) ↦₆₄ s48) ∗
        ((s0.sp - 0x98#64) ↦₆₄ s56w) ∗
        savedCalleeSlots s0)
      (fun sf P_f => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (idSavePollSpec rd pathOk A img stk).post x s0 sf))
      (fun sf P_f => P_f ⊢ (idSavePollSpec rd pathOk A img stk).onPanic x s0 sf) := by
  subst hser
  have hDec' : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idSavePollName +
        bv% (2 ^ 64 + ls_off% "<libsignal_protocol::identity_key::IdentityKey>::decode" -
          ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))
      (identityKeyDecodeSpec A img) := by
    rw [identityKeyDecode_fnAddr_eq]; exact hDec
  have hDealloc := ispoll_dealloc_ok_at hC
  have hsub_hi : saveSubMax getStk putStk ≤ 2 ^ 64 := by
    have : saveMinStk getStk putStk ≤ 2 ^ 64 := le_trans hstk hhi
    unfold saveMinStk at this; omega
  have hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) →
      (P_f ⊢ (idSavePollSpec rd pathOk A img stk).onPanic x s0 sf) :=
    fun _ _ hp => ispoll_onPanic hp
  have hlen33 : k.serialize.length = 33 := by
    simp [IdentityKey.serialize, PublicKey.serialize]
  have hans : IdPeerAns (.ok k.serialize) (.ok (some k)) := by
    cases hcons : k.serialize with
    | nil => simp [hcons] at hlen33
    | cons b rest => exact ⟨k, rfl, hcons⟩
  have hfn : libsignalSessionCode.fnOff idSavePollName =
      num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}") :=
    idSavePoll_fnOff
  code_fetches CryptoVerification.libsignalSessionCode cliIdSavePollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}")) 240
  clear hfn hDec
  dsimp only [tripleRatchetProgAtExt, offAfterGet] at hDec' hDealloc hpc ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr idSavePollName = entry
  examples_hide_fetches
  conv =>
    arg 4
    rw [getResultAt_ok_unpack A s0.sp k.serialize]
    simp only [SpqrV1.ChainProofs.bytesAt, Bool.false_eq_true, ite_false,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap
  apply SepWPp.exists_elim; intro ptr
  refine SepWPp.pure_elim fun ⟨hlen, hcap_lt, hptr⟩ => ?_
  have hcap_ne : cap ≠ 0#64 := by
    intro hc0; subst hc0; simp [hlen33] at hlen
  have hb33 : BitVec.ofNat 64 k.serialize.length = 33#64 := by rw [hlen33]
  conv => arg 4; simp only [hb33]
  apply sepWPp_step_to_frozen hinv (mid := entry +
    bv% (2 ^ 64 + ls_off% "<libsignal_protocol::identity_key::IdentityKey>::decode" -
      ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF_dec hsym_dec
  ispoll_fold_pre (slot90_words4_collapse s0.sp okTagVec cap ptr 33#64)
  conv =>
    arg 4
    rw [stackAt_sub_split (s0.sp - 0xd0#64) (decStk_le_saveSubMax getStk putStk) hsub_hi]
    simp only [sepConj_assoc]
  refine ispoll_call_decode (ret_pc := entry + offAfterDecode)
    hDec' { bytesA := ptr, bytes := k.serialize, ret := s0.sp - 0x90#64 } ?ispollF1
    (by wp_norm_goal) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_goal) (by wp_norm_goal)
    ⟨hF_dec, hsym_dec⟩
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, hlen33]) (by wp_norm_goal)
    hpan ?ispollPre1 ?_
  case ispollPre1 => ispoll_close_frame
  intro sm1 hpc1 hrun1 hsp1 hcs1 hinv1 htr1
  simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm,
    hsp, htr, hx19, hx20, hx24, hx29, hvregs] at hpc1 hsp1 htr1 hcs1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, _, hx23_1, hx24_1, _, _, _, _, hx29_1, hvregs_1⟩
  have hsp_al1 : sm1.spAligned = true := by
    simp only [State.spAligned] at hsp_align ⊢
    rwa [hsp1, ← hsp]
  obtain ⟨w0, h1, b2, d3, d4, d5, b6, hpk_eq⟩ :=
    pointsToBytes_32_exists_pkChunksAt k.publicKey.bytes.toList_length
  conv => arg 4; simp only [State.sp, wp_norm, arm64_norm, hsp, hsp1]
  ispoll_rw_pre (stackAt_sub_split (s0.sp - 0xd0#64) (decStk_le_saveSubMax getStk putStk) hsub_hi).symm
  conv =>
    arg 4
    rw [decodeIdentityKey_serialize k]
    dsimp only [identityKeyResultAt, vecResultAt]
    simp only [ispoll_sp_eqs, hpk_eq, pkChunksAt, sepConj_assoc]
  ispoll_rw_pre (s48_split_byte7 s0.sp s48 s56w)
  conv => arg 4; simp only [sepConj_assoc]
  apply sepWPp_step_to_frozen hinv1 (mid := entry +
    bv% (ls_rel%
      "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"
      "__rustc::__rust_dealloc"))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF_dealloc hsym_dealloc
  have hfree_vec : ((ptr ↦ₛ k.serialize) ∗ vecU8Tail A cap ptr k.serialize) ⊢
      A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := by
    simpa only [SpqrV1.ChainProofs.bytesAt, Bool.false_eq_true, ite_false] using
      vecU8_free_ne (ptr := ptr) A hcap_ne hlen hcap_lt
  ispoll_fold_pre hfree_vec
  conv =>
    arg 4
    rw [stackAt_sub_split (s0.sp - 0xd0#64) (hookStk_le_saveSubMax getStk putStk) hsub_hi]
    simp only [sepConj_assoc]
  refine ispoll_call_dealloc (ret_pc := entry + offAfterDealloc)
    hDealloc ptr cap.toNat ?ispollF2
    (by wp_norm_goal) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_goal) (by wp_norm_goal)
    ⟨hF_dealloc, hsym_dealloc⟩
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
    (layoutOk_u8_of_ne_zero hcap_ne hcap_lt) hpan
    ?ispollPre2 ?_
  case ispollPre2 => ispoll_close_frame
  intro sm2 hpc2 hrun2 hsp2 hcs2 hinv2 htr2
  simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm,
    hsp1, htr1, hx19_1, hx20_1, hx21_1, hx23_1, hx24_1, hx29_1, hvregs_1] at hpc2 hsp2 htr2 hcs2
  rcases hcs2 with ⟨hx19_2, hx20_2, _, hx22_2, _, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
  have hsp_al2 : sm2.spAligned = true := by
    simp only [State.spAligned] at hsp_align ⊢
    rwa [hsp2, ← hsp]
  conv => arg 4; simp only [State.sp, wp_norm, arm64_norm, hsp, hsp1, hsp2]
  have hpk88_fold :
      (((s0.sp - 0x90#64) ↦₆₄ okTagVec) ∗
        ((s0.sp - 0x88#64) ↦₃₂ w0) ∗ ((s0.sp - 0x84#64) ↦₁₆ h1) ∗ ((s0.sp - 0x82#64) ↦₈ b2) ∗
        ((s0.sp - 0x81#64) ↦₆₄ d3) ∗ ((s0.sp - 0x79#64) ↦₆₄ d4) ∗ ((s0.sp - 0x71#64) ↦₆₄ d5) ∗
        ((s0.sp - 0x69#64) ↦₈ b6) ∗ memRegion (s0.sp - 0x68#64) 8) ⊢
      memRegion (s0.sp - 0x90#64) 32 ∗ memRegion (s0.sp - 0x70#64) 16 := by
    have h := slot90_pk88_to_32_16 s0.sp okTagVec w0 h1 b2 d3 d4 d5 b6
    unfold pkChunksAt at h
    simpa only [ispoll_sp_eqs, sepConj_assoc] using h
  ispoll_fold_pre hpk88_fold
  ispoll_rw_pre (stackAt_sub_split (s0.sp - 0xd0#64) (hookStk_le_saveSubMax getStk putStk) hsub_hi).symm
  change SepWPp (tripleRatchetProgAtExt img.base ext) _ _ _ _ _
  refine sepWPp_conseq ?_
    (ispoll_branch_ok_some_220_gen (rd := rd) (pathOk := pathOk) hC hPut
      (by dsimp only [tripleRatchetProgAtExt]; rw [hentry]; exact hEqAt) heq_le hstk hhi x k
      c1 c2 c3 c4 c5 c6 c7 c15 s16 s24 s32 s40 s56w
      w0 h1 b2 d3 d4 d5 b6 hpk_eq
      (by dsimp only [tripleRatchetProgAtExt]; rw [hentry]; exact hpc2)
      hrun2 hsp2 hsp_al2 hvregs_2 htr2 hinv2
      hx19_2 hx20_2 hx22_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2
      hnlen hclen hgr hans)
  exact Entails.of_eq (by ispoll_ac_rfl)

/-- `Ok k.serialize` branch after `Dir::get` returns at `+68` (`gr = .ok k.serialize`). -/
theorem ispoll_branch_ok_some {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {getStk putStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hPut : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutStrName)
      (dirPutStrSpec A img putStk))
    (hDec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyDecodeName)
      (identityKeyDecodeSpec A img))
    (hEq : Getters.PublicKeyEqOkExt img.base ext)
    (hstk : saveMinStk getStk putStk ≤ stk)
    (hhi : stk ≤ 2 ^ 64)
    {s0 s : State} (x : IdPollGhost) (k : IdentityKey) {bs : List (BitVec 8)}
    (c1 c2 c3 c4 c5 c6 c7 c15 : BitVec 8)
    (s16 : BitVec 64) (s24 : BitVec 8) (s32 : BitVec 64) (s40 : BitVec 8)
    (s48 s56w : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr idSavePollName + offAfterGet)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0xd0#64)
    (hsp_align : s.spAligned = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace)
    (hinv : ImgCallInv img s)
    (hx19 : s.readReg64 .x19 = x.call.fut)
    (hx20 : s.readReg64 .x20 = x.call.out)
    (hx24 : s.readReg64 .x24 = x.self)
    (hx29 : s.readReg64 .x29 = s0.sp - 0x60#64)
    (hnlen : x.call.call.addr.name.bytes.length < 2 ^ 32)
    (hclen : x.peers.changed.length < 2 ^ 32)
    (hser : k.serialize = bs)
    (hgr : Except.ok bs = x.peers.get rd s0.fs.files x.call.call.addr.val.name) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s
      (getResultAt A (s0.sp - 0x90#64) (.ok bs) ∗
        dirAt A (x.self + 0x28#64) x.peers ∗
        memRegion x.call.out 48 ∗
        idSaveBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 0#8 ∗
        protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
        (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗
        logOff img ∗ A.pool ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - saveMinStk getStk putStk) ∗
        stackAt (s0.sp - 0xd0#64) (saveSubMax getStk putStk) ∗
        memRegion (s0.sp - 0xd0#64) 8 ∗
        overlap7View1 (s0.sp - 0xc8#64) c1 c2 c3 c4 c5 c6 c7 ∗
        ((s0.sp - 0xc1#64) ↦₈ c15) ∗
        ((s0.sp - 0xc0#64) ↦₆₄ s16) ∗
        ((s0.sp - 0xb8#64) ↦₈ s24) ∗
        memRegion (s0.sp - 0xb7#64) 7 ∗
        ((s0.sp - 0xb0#64) ↦₆₄ s32) ∗
        ((s0.sp - 0xa8#64) ↦₈ s40) ∗
        memRegion (s0.sp - 0xa7#64) 7 ∗
        ((s0.sp - 0xa0#64) ↦₆₄ s48) ∗
        ((s0.sp - 0x98#64) ↦₆₄ s56w) ∗
        savedCalleeSlots s0)
      (fun sf P_f => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (idSavePollSpec rd pathOk A img stk).post x s0 sf))
      (fun sf P_f => P_f ⊢ (idSavePollSpec rd pathOk A img stk).onPanic x s0 sf) :=
  ispoll_branch_ok_some_gen hC hPut hDec (ispoll_publicKeyEq_ok_at_64 hEq)
    (eqStk_le_saveSubMax getStk putStk) hstk hhi x k
    c1 c2 c3 c4 c5 c6 c7 c15 s16 s24 s32 s40 s48 s56w
    hpc hrun hsp hsp_align hvregs htr hinv hx19 hx20 hx24 hx29
    hnlen hclen hser hgr

end CryptoVerification.SignalSession.Cli.Store.IdSavePoll.Helpers

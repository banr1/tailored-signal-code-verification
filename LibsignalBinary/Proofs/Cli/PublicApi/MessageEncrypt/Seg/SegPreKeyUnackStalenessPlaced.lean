/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyCommonPlaced
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyUnackStaleness
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `segPreKey` Unacknowledged Items Getter and Staleness Check (`+0x344..+0x6fc`)

Defines `StalenessDurStatePlaced` (`+0x6c4`) and `StalenessAddStatePlaced` (`+0x6fc`) and proves
`segPreKey_unackItems_to_dur_placed_ok` and `segPreKey_staleness_to_add_placed_ok` on Block `464`
(`lsProg_464 Hk`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.CliRatchet.EncPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.UnackItems
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet
  (lsRetAddr624_of_lr_eq_blockPlacement_base_add)

attribute [local irreducible] Program.fetch Program.externAt?

/-! ## 1. `+0x344..+0x6c4`: `StalenessDurStatePlaced` & `segPreKey_unackItems_to_dur_placed_ok` -/

def pollWithBaseKey_trap_placed (sp : BitVec 64) (items : PendingPreKey) (ts : SystemTime) : SepProp :=
  memRegion (sp + 0x46a#64) 0x64a ∗
    ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
    memRegion (sp + 0xad4#64) 0x2c ∗
    ((sp + 0xb00#64) ↦₆₄ ts.tvSec) ∗
    ((sp + 0xb08#64) ↦₃₂ ts.tvNsec) ∗
    memRegion (sp + 0xb0c#64) 4 ∗
    memRegion (sp + 0xb10#64) 0x70

theorem poll_unackItems_pack_pollWithBaseKey_trap (sp : BitVec 64) (items : PendingPreKey)
    (ts : SystemTime) :
    (memRegion (sp + 0x46a#64) 0x116 ∗
      memRegion (sp + 0x580#64) 88 ∗
      memRegion (sp + 0x5d8#64) 0x298 ∗
      memRegion (sp + 0x870#64) 36 ∗
      memRegion (sp + 0x894#64) 0x21c ∗
      memRegion (sp + 0xab0#64) 4 ∗
      ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
      memRegion (sp + 0xad4#64) 0x2c ∗
      ((sp + 0xb00#64) ↦₆₄ ts.tvSec) ∗
      ((sp + 0xb08#64) ↦₃₂ ts.tvNsec) ∗
      memRegion (sp + 0xb0c#64) 4 ∗
      memRegion (sp + 0xb10#64) 0x70) ⊢
    pollWithBaseKey_trap_placed sp items ts := by
  unfold pollWithBaseKey_trap_placed
  rw [mr_cut_add sp 0x46a 0x116 0x534 (by decide),
      mr_cut_add sp 0x580 88 0x4dc (by decide),
      mr_cut_add sp 0x5d8 0x298 0x244 (by decide),
      mr_cut_add sp 0x870 36 0x220 (by decide),
      mr_cut_add sp 0x894 0x21c 4 (by decide)]
  simp only [sepConj_assoc]
  exact Entails.refl _

theorem pollWithBaseKey_dur_unpack_trap (sp : BitVec 64) (items : PendingPreKey)
    (ts : SystemTime) :
    pollWithBaseKey_trap_placed sp items ts =
      memRegion (sp + 0x46a#64) 0x116 ∗
      memRegion (sp + 0x580#64) 24 ∗
      memRegion (sp + 0x598#64) 0x300 ∗
      memRegion (sp + 0x898#64) 8 ∗
      memRegion (sp + 0x8a0#64) 0x214 ∗
      ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
      memRegion (sp + 0xad4#64) 0x2c ∗
      ((sp + 0xb00#64) ↦₆₄ ts.tvSec) ∗
      ((sp + 0xb08#64) ↦₃₂ ts.tvNsec) ∗
      memRegion (sp + 0xb0c#64) 4 ∗
      memRegion (sp + 0xb10#64) 0x70 := by
  unfold pollWithBaseKey_trap_placed
  rw [mr_cut_add sp 0x46a 0x116 0x534 (by decide),
      mr_cut_add sp 0x580 24 0x51c (by decide),
      mr_cut_add sp 0x598 0x300 0x21c (by decide),
      mr_cut_add sp 0x898 8 0x214 (by decide)]
  simp only [sepConj_assoc]

theorem durationSinceBounded_b00_intro_trap (sp : BitVec 64) (tvSec : BitVec 64)
    (tvNsec : BitVec 32) (hns : tvNsec.toNat < 1000000000) :
    (((sp + 0xb00#64) ↦₆₄ tvSec) ∗ ((sp + 0xb08#64) ↦₃₂ tvNsec) ∗ memRegion (sp + 0xb0c#64) 4) ⊢
      (∃∗ tvSec : BitVec 64, ∃∗ tvNsec : BitVec 32,
        ⌜tvNsec.toNat < 1000000000⌝ ∗
        ((sp + 0xb00#64) ↦₆₄ tvSec) ∗ (((sp + 0xb00#64) + 8#64) ↦₃₂ tvNsec) ∗
        memRegion ((sp + 0xb00#64) + 12#64) 4) := by
  refine Entails.sepExists_right tvSec (Entails.sepExists_right tvNsec ?_)
  refine Entails.pure_right hns ?_
  simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using Entails.refl _

/-- State at `+0x6c4` (`encEntryPlaced + 0x6c4#64`), right before `bl durationSince`,
    under `[LibsignalPlacement]`. -/
def StalenessDurStatePlaced [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (ctl : BitVec 64)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (items : PendingPreKey) (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (ts : SystemTime) (pkVal kyIdVal : BitVec 32) (kyPtr kyLen : BitVec 64)
    (R0 : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 0xbe0#64
  SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat = some ts ∧
  optU32ValProp items.preKeyId pkVal ∧
  optU32ValProp (sess.pendingKyberPreKey.map (·.preKeyId)) kyIdVal ∧
  unackKyberSliceProp G.kyber kyPtr kyLen ∧
  s.pc = encEntryPlaced + 0x6c4#64 ∧
  encMidMetaPlaced x s0 s ∧
  s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)) ∧
  s.readReg64 .x0 = sp + 0xb00#64 ∧
  (s.readReg64 .x2).setWidth 32 = 0#32 ∧
  s.readReg64 .x8 = sp + 0x580#64 ∧
  s.readReg64 .x20 = sp + 0x58#64 ∧
  (s.readReg64 .x21).setWidth 32 = ts.tvNsec ∧
  s.readReg64 .x22 = sp + 0x8b8#64 ∧
  s.readReg64 .x23 = kyPtr ∧
  (s.readReg64 .x24).setWidth 32 = (if items.preKeyId.isSome then 1#32 else 0#32) ∧
  s.readReg64 .x25 = sp + 0x580#64 ∧
  s.readReg64 .x26 = sp + 0x9d0#64 ∧
  s.readReg64 .x27 = ts.tvSec ∧
  s.readReg64 .x28 = sp + 0x4a0#64 ∧
  x.ptext.length < 2 ^ 32 ∧ x.rest.length < 2 ^ 63 ∧ x.locA ≠ 0#64 ∧
  x.now.tvNsec.toNat < 10 ^ 9 ∧ withStoresEncStack ≤ s0.sp.toNat ∧
  (s.mem ⊨
    vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
    sessionStateReprAt A (sp + 0x128#64) G { sess with state := taken } ∗
    ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
    ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
    otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
    ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
    memRegion (sp + 0x370#64) 0xf8 ∗
    preKeyScratch sp kyLen items.signedPreKeyId kyIdVal pkVal sess.pendingKyberPreKey ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
    pollWithBaseKey_trap_placed sp items ts ∗
    memRegion x.ret 248 ∗
    encCommonPlaced A ctl x 0 s0 ∗ (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0))

set_option maxHeartbeats 800000 in
theorem segPreKey_unackItems_to_dur_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (env : EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord Hk)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (items : PendingPreKey) (R0 : SepProp) (s0 s : State)
    (hpk : sess.pendingPreKey = some items)
    (hkey : KeyStateVPlaced kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k R0 s0 s) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R0 s0 s
      (fun s' => ∃ prevCap prevPtr G ts pkVal kyIdVal kyPtr kyLen,
        StalenessDurStatePlaced kit st0 ikit ist0 ctl encRecord x r sess otr taken pqCap pqPtr k items
          prevCap prevPtr G ts pkVal kyIdVal kyPtr kyLen R0 s0 s') := by
  rcases hkey with ⟨hcur, hscope, hotr, hrem, hpc, hmeta, htr, hregs, hptlen, hrestlen, hlocA, hnow, hstack, hmem⟩
  rcases hregs with ⟨hx0, hx8, hx20, hx22, hx23, hx25, hx26, hx27, hx28⟩
  rcases hmeta with ⟨hstat, hsp, hsp0Al, hspAl, hx29, hx19, hcrl, hvregs⟩
  rw [sp_sub_60_eq_add_b80 s0.sp] at hx29
  set sp := s0.sp - 0xbe0#64
  unfold keyPCPlaced encEntryPlaced at hpc
  have hunack := env.callees.unack
  clear env
  apply segExitPlaced_of_sepWPp_lscro hcrl
    (target := (blkPl_464).base + 0x6c4#64)
    (encSeam_mem_group hmem)
  dsimp only [takenSlots, encCommonPlaced]
  rw [poll_unackItems_regions sp, encSubStack_split_unack hsp]
  refine SepWPp.fold (takenRecord_sessionRecordAt_unpack A sp sess taken) (by sep_focus) ?_
  refine sepWPp_elim_ex fun prevCap => sepWPp_elim_ex fun prevPtr => sepWPp_elim_ex fun G => ?_
  dsimp only [lsProg_464, ite_true] at hunack ⊢
  apply CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.SepWPp.of_sepWP (mid := lsmpl.base 36)
  wp_step
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  refine SepWPp.call_frame_rocl hunack
    (x := (⟨sp + 0x128#64, G, { sess with state := taken }, sp + 0x580#64⟩ : UnackCall))
    (by wp_norm_goal) (by wp_norm_goal) hspAl
    (show _ = (blkPl_464).base + 0x348#64 by rfl)
    hcrl rfl ⟨by simp_all, by simp_all⟩
    (by dsimp [State.sp, State.setPC, State.writeReg64, State.readReg64]; sep_focus)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun sf _ hm => by
      rw [sepConj_assoc] at hm
      exact onPanic_of_unack_placed htr hcur hscope hotr hrem hpk hm)
    fun s1 hpc1 hstat1 hsp1 hcs1 _hcrl1 => ?_
  dsimp only [unackItemsPlacedSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_
  have hcs1' := calleeSavedPreserved_after_bl hcs1; clear hcs1
  rcases hcs1' with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  rw [hx19] at hx19_1; rw [hx20] at hx20_1; rw [hx22] at hx22_1
  rw [hx25] at hx25_1; rw [hx26] at hx26_1; rw [hx28] at hx28_1; rw [hx29] at hx29_1; rw [hvregs] at hvregs_1
  rw [sp_after_bl] at hsp1
  rw [trace_after_bl] at htr1
  have hsp1_al : s1.spAligned = true := by
    unfold State.spAligned at hspAl ⊢; rwa [hsp1]
  rw [hsp] at hsp1
  rw [htr] at htr1
  refine SepWPp.fold (unackOutAt_taken_some sp G.kyber sess items hpk) (by sep_focus) ?_
  refine sepWPp_elim_ex fun ts => ?_
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun hts => ?_
  refine sepWPp_fold_ex1 (optU32At_unpack32 (sp + 0x580#64) items.preKeyId) (by sep_focus)
    fun pkVal hpkVal => ?_
  refine sepWPp_fold_ex1 (optU32At_unpack64 (sp + 0x588#64) (sess.pendingKyberPreKey.map (·.preKeyId)))
    (by sep_focus) fun kyIdVal hkyIdVal => ?_
  refine sepWPp_fold_ex5 (baseKeyShift_unpack_59c sp items.baseKey) (by sep_focus)
    fun bk0 bk1 bk2 bk3 bk4 hbk => ?_
  refine sepWPp_fold_ex2 (unackKyberSliceAt_unpack (sp + 0x5c0#64) G.kyber) (by sep_focus)
    fun kyPtr kyLen hkySlice => ?_
  refine SepWPp.fold (curScratch_unackItems_unpack sp) (by sep_focus) ?_
  refine sepWPp_elim_ex fun s48 => sepWPp_elim_ex fun s40 => sepWPp_elim_ex fun s38 =>
    sepWPp_elim_ex fun s34 => sepWPp_elim_ex fun s28 => sepWPp_elim_ex fun s24 =>
    sepWPp_elim_ex fun s18 => ?_
  refine SepWPp.fold (memRegion_36_unpack (sp + 0x870#64)) (by sep_focus) ?_
  refine sepWPp_elim_ex fun w890 => sepWPp_elim_ex fun w888 => sepWPp_elim_ex fun w880 =>
    sepWPp_elim_ex fun w878 => sepWPp_elim_ex fun w870 => ?_
  refine SepWPp.fold (memRegion_36_unpack (sp + 0xab0#64)) (by sep_focus) ?_
  refine sepWPp_elim_ex fun wad0 => sepWPp_elim_ex fun wac8 => sepWPp_elim_ex fun wac0 =>
    sepWPp_elim_ex fun wab8 => sepWPp_elim_ex fun wab0 => ?_
  refine SepWPp.fold (memRegion_16_ts_unpack_b00 sp) (by sep_focus) ?_
  refine sepWPp_elim_ex fun wb08 => sepWPp_elim_ex fun wb00 => ?_
  apply CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.SepWPp.of_sepWP_ret
  wp_steps
  refine SepWP.fold (baseKeyShift_pack_ab0 sp items.baseKey bk0 bk1 bk2 bk3 bk4 hbk) (by sep_focus) ?_
  refine SepWP.fold (cells36_entails_memRegion_36_870 sp bk0 bk1 bk2 bk3 bk4) (by sep_focus) ?_
  refine SepWP.fold
    (unackOut_cells_entails_memRegion_88_580 sp _ pkVal _ ts.tvSec ts.tvNsec bk0 bk1 bk2 bk3 bk4 kyPtr kyLen items.signedPreKeyId)
    (by sep_focus) ?_
  refine SepWP.fold (poll_unackItems_pack_pollWithBaseKey_trap sp items ts) (by sep_focus) ?_
  refine sepWP_fold_preKeyScratch sp kyLen _ items.signedPreKeyId kyIdVal pkVal sess.pendingKyberPreKey
    (by sep_focus) (by rfl) ?_
  refine SepWP.fold (encSubStack_pack_unack hsp _ _) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl_f hmf
  dsimp only [StalenessDurStatePlaced, encEntryPlaced, sp]
    at hsp1 hx19_1 hx20_1 hx22_1 hx25_1 hx26_1 hx28_1 hx29_1 hvregs_1 hmf ⊢
  refine ⟨prevCap, prevPtr, G, ts, pkVal, kyIdVal, kyPtr, kyLen,
    hts, hpkVal, hkyIdVal, hkySlice, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hptlen, hrestlen, hlocA, hnow, hstack, ?_⟩
  · wp_norm_goal
  · refine ⟨by wp_norm_goal, by wp_norm_goal, hsp0Al,
      by unfold State.spAligned at hsp0Al ⊢; wp_norm_goal; exact hsp0Al,
      by rw [sp_sub_60_eq_add_b80 s0.sp]; wp_norm_goal,
      by wp_norm_goal, hcrl_f, by wp_norm_goal⟩
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · cases items.preKeyId <;> wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · dsimp only [encCommonPlaced, encSpillsAtV] at hmf ⊢; arm64_sep_close

/-! ## 2. `+0x6c4..+0x6fc`: `StalenessAddStatePlaced` & `segPreKey_staleness_to_add_placed_ok` -/

/-- State at `+0x6fc` (`encEntryPlaced + 0x6fc#64`), right after `bl timeAdd`,
    under `[LibsignalPlacement]`. -/
def StalenessAddStatePlaced [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (ctl : BitVec 64)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (items : PendingPreKey) (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (ts expiry : SystemTime) (pkVal kyIdVal : BitVec 32) (kyPtr kyLen : BitVec 64)
    (R0 : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 0xbe0#64
  SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat = some ts ∧
  ts.checkedAddSecs maxUnacknowledgedSessionAge = some expiry ∧
  optU32ValProp items.preKeyId pkVal ∧
  optU32ValProp (sess.pendingKyberPreKey.map (·.preKeyId)) kyIdVal ∧
  unackKyberSliceProp G.kyber kyPtr kyLen ∧
  s.pc = encEntryPlaced + 0x6fc#64 ∧
  encMidMetaPlaced x s0 s ∧
  s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)) ∧
  s.readReg64 .x0 = expiry.tvSec ∧
  (s.readReg64 .x1).setWidth 32 = expiry.tvNsec ∧
  s.readReg64 .x20 = sp + 0x58#64 ∧
  (s.readReg64 .x21).setWidth 32 = ts.tvNsec ∧
  s.readReg64 .x22 = sp + 0x8b8#64 ∧
  s.readReg64 .x23 = kyPtr ∧
  (s.readReg64 .x24).setWidth 32 = (if items.preKeyId.isSome then 1#32 else 0#32) ∧
  s.readReg64 .x25 = sp + 0x580#64 ∧
  s.readReg64 .x26 = sp + 0x9d0#64 ∧
  s.readReg64 .x27 = ts.tvSec ∧
  s.readReg64 .x28 = sp + 0x4a0#64 ∧
  x.ptext.length < 2 ^ 32 ∧ x.rest.length < 2 ^ 63 ∧ x.locA ≠ 0#64 ∧
  x.now.tvNsec.toNat < 10 ^ 9 ∧ withStoresEncStack ≤ s0.sp.toNat ∧
  (s.mem ⊨
    vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
    sessionStateReprAt A (sp + 0x128#64) G { sess with state := taken } ∗
    ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
    ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
    otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
    ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
    memRegion (sp + 0x370#64) 0xf8 ∗
    preKeyScratch sp kyLen items.signedPreKeyId kyIdVal pkVal sess.pendingKyberPreKey ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
    pollWithBaseKey sp items ∗
    memRegion x.ret 248 ∗
    encCommonPlaced A ctl x 0 s0 ∗ (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0))

set_option maxHeartbeats 800000 in
theorem segPreKey_staleness_to_add_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (env : EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord Hk)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (items : PendingPreKey) (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (ts : SystemTime) (pkVal kyIdVal : BitVec 32) (kyPtr kyLen : BitVec 64)
    (R0 : SepProp) (s0 s : State)
    (hcur : r.currentSession = some sess)
    (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hotr : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hdur : StalenessDurStatePlaced kit st0 ikit ist0 ctl encRecord x r sess otr taken pqCap pqPtr k items
      prevCap prevPtr G ts pkVal kyIdVal kyPtr kyLen R0 s0 s) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R0 s0 s
      (fun s' => ∃ expiry,
        StalenessAddStatePlaced kit st0 ikit ist0 ctl encRecord x r sess otr taken pqCap pqPtr k items
          prevCap prevPtr G ts expiry pkVal kyIdVal kyPtr kyLen R0 s0 s') := by
  rcases hdur with ⟨hts, hpkVal, hkyIdVal, hkySlice, hpc, hmeta, htr,
    hx0, hx2, hx8, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28,
    hptlen, hrestlen, hlocA, hnow, hstack, hmem⟩
  rcases hmeta with ⟨hstat, hsp, hsp0Al, hspAl, hx29, hx19, hcrl, hvregs⟩
  have hts_nsec : ts.tvNsec.toNat < 10 ^ 9 := (unixEpoch_checkedAddSecs_tvNsec hts).2
  set sp := s0.sp - 0xbe0#64
  unfold encEntryPlaced at hpc
  have hdur_call := subroutine_ok_merge_withLsRet (fun _ _ => rfl) (durationSince_placed_ok_at_enc env)
  have hadd_call := subroutine_ok_merge_withLsRet (fun _ _ => rfl) (timeAdd_placed_ok_at_enc env)
  clear env
  apply segExitPlaced_of_sepWPp_lscro hcrl
    (target := (blkPl_464).base + 0x6fc#64)
    (dur_mem_group hmem)
  dsimp only [encCommonPlaced]
  rw [pollWithBaseKey_dur_unpack_trap sp items ts, encSubStack_split_ext hsp]
  refine SepWPp.fold (durationSinceBounded_b00_intro_trap sp ts.tvSec ts.tvNsec hts_nsec) (by sep_focus) ?_
  dsimp only [lsProg_464, ite_true] at hdur_call hadd_call ⊢
  apply CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.SepWPp.of_sepWP (mid := lsρ lsDurationSinceSym)
  wp_step
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  refine CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.SepWPp.call_frame hdur_call
    (x := (sp + 0xb00#64, sp + 0x580#64))
    (by wp_norm_goal) (by wp_norm_goal) hspAl
    (show _ = (blkPl_464).base + 0x6c8#64 by rfl)
    rfl
    ⟨lsRetAddr624_of_lr_eq_blockPlacement_base_add 464 1736#64 rfl,
      by simp_all, by simp_all, by dsimp [State.setPC, State.writeReg64, State.readReg64, Reg.x2] at hx2 ⊢; rw [hx2]; decide⟩
    (by dsimp [State.sp, State.setPC, State.writeReg64, State.readReg64]; sep_focus)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun _ _ hm => by
      dsimp only [durationSinceBoundedSpec, Spec.onPanic] at hm
      rw [sepConj_assoc] at hm
      exact (not_satisfies_false_sepConj hm).elim)
    fun s1 hpc1 hstat1 hsp1 hcs1 => ?_
  dsimp only [durationSinceBoundedSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_
  refine SepWPp.fold (stackAt_eq_sp hsp1) (by sep_focus) ?_
  have hcs1' := calleeSavedPreserved_after_bl hcs1; clear hcs1
  rcases hcs1' with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  rw [hx19] at hx19_1; rw [hx20] at hx20_1; rw [hx22] at hx22_1; rw [hx23] at hx23_1
  rw [hx25] at hx25_1; rw [hx26] at hx26_1; rw [hx27] at hx27_1; rw [hx28] at hx28_1; rw [hx29] at hx29_1; rw [hvregs] at hvregs_1
  have hx21_1' : (s1.readReg64 .x21).setWidth 32 = ts.tvNsec := by
    change (s1.readReg64 (.gpr 21#5)).setWidth 32 = ts.tvNsec; rw [hx21_1]; exact hx21
  have hx24_1' : (s1.readReg64 .x24).setWidth 32 = (if items.preKeyId.isSome then 1#32 else 0#32) := by
    change (s1.readReg64 (.gpr 24#5)).setWidth 32 = _; rw [hx24_1]; exact hx24
  rw [sp_after_bl] at hsp1
  rw [trace_after_bl] at htr1
  have hsp1_al : s1.spAligned = true := by
    unfold State.spAligned at hspAl ⊢; rwa [hsp1]
  rw [hsp] at hsp1
  rw [htr] at htr1
  refine SepWPp.fold (dur_ret_24_unpack sp) (by sep_focus) ?_
  refine sepWPp_elim_ex fun w588 => sepWPp_elim_ex fun w580 => ?_
  refine SepWPp.fold (memRegion_8_898_unpack sp) (by sep_focus) ?_
  refine sepWPp_elim_ex fun w898 => ?_
  apply CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.SepWPp.of_sepWP (mid := lsρ lsTimeAddSym)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  refine CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.SepWPp.call_frame hadd_call
    (x := (ts, maxUnacknowledgedSessionAge))
    (by wp_norm_goal) (by wp_norm_goal)
    (by unfold State.spAligned at hsp1_al ⊢; rw [hsp1] at hsp1_al; wp_norm_goal)
    (show _ = (blkPl_464).base + 0x6fc#64 by wp_norm_goal)
    rfl
    ⟨lsRetAddr624_of_lr_eq_blockPlacement_base_add 464 1788#64 (by wp_norm_goal),
      by wp_norm_goal, by wp_norm_goal, hts_nsec, by wp_norm_goal, by wp_norm_goal⟩
    (by dsimp [State.sp, State.setPC, State.setMem, State.setPState, State.writeReg64, State.readReg64]; sep_focus)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun sf _ hm => by
      rw [sepConj_assoc] at hm
      refine onPanic_of_timeAdd_placed (s := _) ?_ hcur hscope hotr hrem hpk hts hm
      wp_norm_goal)
    fun s2 hpc2 hstat2 hsp2 hcs2 => ?_
  dsimp only [timeAddSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hexp, htr2⟩ => ?_
  refine SepWPp.fold (stackAt_eq_sp hsp2) (by sep_focus) ?_
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
  simp only [wp_norm, arm64_norm]
    at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 hvregs_2 hsp2 htr2
  rw [hx19_1] at hx19_2; rw [hx20_1] at hx20_2; rw [hx22_1] at hx22_2; rw [hx23_1] at hx23_2
  rw [hx25_1] at hx25_2; rw [hx26_1] at hx26_2; rw [hx27_1] at hx27_2; rw [hx28_1] at hx28_2; rw [hx29_1] at hx29_2; rw [hvregs_1] at hvregs_2
  have hx21_2' : (s2.readReg64 .x21).setWidth 32 = ts.tvNsec := by
    change (s2.readReg64 (.gpr 21#5)).setWidth 32 = ts.tvNsec; rw [hx21_2]; exact hx21_1'
  have hx24_2' : (s2.readReg64 .x24).setWidth 32 = (if items.preKeyId.isSome then 1#32 else 0#32) := by
    change (s2.readReg64 (.gpr 24#5)).setWidth 32 = _; rw [hx24_2]; exact hx24_1'
  rw [hsp1] at hsp2
  rw [htr1] at htr2
  apply CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.SepWPp.of_sepWP_ret
  refine SepWP.fold (pollWithBaseKey_dur_pack sp items w580 w588 _) (by sep_focus) ?_
  have hsp2_pack :
      (memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
        stackAt s2.sp extHookStack) ⊢ stackAt sp encSubStack := by
    rw [hsp2, ← encSubStack_split_ext rfl]
    exact Entails.refl _
  refine SepWP.fold hsp2_pack (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl_f hmf
  dsimp only [StalenessAddStatePlaced, encEntryPlaced, sp]
    at hsp2 hx19_2 hx20_2 hx22_2 hx25_2 hx26_2 hx28_2 hx29_2 hvregs_2 hmf ⊢
  refine ⟨⟨s2.readReg64 .x0, (s2.readReg64 .x1).setWidth 32⟩,
    hts, hexp, hpkVal, hkyIdVal, hkySlice, hpc2, ?_, htr2, rfl, rfl,
    hx20_2, hx21_2', hx22_2, hx23_2, hx24_2', hx25_2, hx26_2, hx27_2, hx28_2,
    hptlen, hrestlen, hlocA, hnow, hstack, ?_⟩
  · refine ⟨hstat2, hsp2, hsp0Al,
      by unfold State.spAligned at hsp0Al ⊢; rw [hsp2]; wp_norm_goal,
      hx29_2, hx19_2, hcrl_f, hvregs_2⟩
  · dsimp only [encCommonPlaced] at hmf ⊢; arm64_sep_close

end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey

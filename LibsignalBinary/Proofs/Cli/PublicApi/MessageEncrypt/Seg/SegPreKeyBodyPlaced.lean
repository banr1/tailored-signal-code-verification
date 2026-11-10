/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyTailPlaced
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyBody
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `segPreKey` Registration IDs, Kyber Closure, and Segment Assembly

Proves `segPreKey_regId_kyber_placed_ok` (`+0x6fc..+0x8b4`, calling `kyberMap` on Block `430`) on
Block `464` (`lsProg_464 Hk`) under `[LibsignalPlacement]`, and assembles `segPreKey_placed_okV`.
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

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem lsLogOff_eq [LibsignalPlacement] :
    FromRecordCallees.lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) := rfl

/-! ## 1. E6b + Kyber Closure (`+0x6fc..+0x8b4`) on Block `464` (`lsProg_464 Hk`) -/

set_option maxHeartbeats 800000 in
theorem segPreKey_regId_kyber_placed_ok [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (env : EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord Hk)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (items : PendingPreKey)
    (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (ts expiry : SystemTime) (pkVal kyIdVal : BitVec 32) (kyPtr kyLen : BitVec 64)
    (R : SepProp) (s0 s : State)
    (hcur : r.currentSession = some sess)
    (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hlt : expiry.lt x.now = false)
    (hadd : StalenessAddStatePlaced kit st0 ikit ist0 ctl encRecord x r sess otr taken pqCap pqPtr k items
      prevCap prevPtr G ts expiry pkVal kyIdVal kyPtr kyLen R s0 s) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s
      (PreKeyEncryptStatePlaced kit st0 ikit ist0 ctl encRecord x r sess otr taken pqCap pqPtr k items R s0) := by
  rcases hadd with ⟨hts, hexp, hpkVal, hkyIdVal, hkySlice, hpc, hmeta, htr,
    hx0, hx1, hx20, _hx21, hx22, hx23, hx24, hx25, hx26, _hx27, hx28,
    hptlen, hrestlen, hlocA, hnow, hstack, hmem⟩
  rcases hmeta with ⟨hstat, hsp, hsp0Al, hspAl, hx29, hx19, hcrl, hvregs⟩
  have hky_bound := (env.scopeIn r hscope sess hcur).2.2.2
  set sp := s0.sp - 0xbe0#64
  unfold encEntryPlaced at hpc
  have hkyber_call := env.callees.kyber
  clear env
  apply segExitPlaced_of_sepWPp_lscro hcrl
    (target := (blkPl_464).base + 2228#64)
    (dur_mem_group hmem)
  refine SepWPp.fold (sessionAt_regId_unpack A sp G sess taken) (by sep_focus) ?_
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun hkyRel => ?_
  refine SepWPp.fold
    (preKeyScratch_regId_unpack sp kyLen items.signedPreKeyId kyIdVal pkVal sess.pendingKyberPreKey)
    (by sep_focus) ?_
  refine sepWPp_elim_ex fun w14 => ?_
  refine SepWPp.fold (pollWithBaseKey_regId_unpack sp items) (by sep_focus) ?_
  refine sepWPp_elim_ex fun w590 => sepWPp_elim_ex fun w588 => sepWPp_elim_ex fun w580 => ?_
  dsimp only [encSpillsAt, encSpillsAtV, encCommonPlaced, nowAt, lsLogOff_eq]
  rw [encSubStack_split_kyber hsp]
  dsimp only [lsProg_464, ite_true] at hkyber_call ⊢
  cases hky : sess.pendingKyberPreKey with
  | none =>
    cases hGky : G.kyber with
    | some g =>
      rw [hGky, hky] at hkyRel
      exact False.elim hkyRel
    | none =>
      rw [hGky] at hkySlice
      dsimp only [unackKyberSliceProp] at hkySlice
      subst hkySlice
      apply StoreKit.sepWPp_seq_lscro hcrl (mid := lsmpl.base 430)
      wp_steps
      refine SepWP.fold (kyberArgAt_none_pack sp w580 w590) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hcrl_call
      refine SepWPp.call_frame_rocl hkyber_call
        (x := ⟨sp + 0x8a0#64, sp + 0x580#64, 0#64, none⟩)
        (by wp_norm_goal) (by wp_norm_goal)
        (by dsimp [State.spAligned, State.sp, State.setPC, State.setMem, State.setPState, State.writeReg64, State.readReg64]; exact hspAl)
        (show _ = (blkPl_464).base + 2228#64 by wp_norm_goal)
        hcrl_call
        rfl ⟨by wp_norm_goal, by wp_norm_goal⟩
        (by dsimp [State.sp, State.setPC, State.setMem, State.setPState, State.writeReg64, State.readReg64]; sep_focus)
        (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
        (fun sf _ hm => by
          rw [sepConj_assoc] at hm
          refine onPanic_of_alloc_placed (s := _) ?_ hm
          change s0.trace <+: s.trace
          rw [htr]
          exact ⟨kit.loadEvs encRecord x.rem.val (.ok (some r)), rfl⟩)
        fun s1 hpc1 hstat1 hsp1 hcs1 _hcrl1 => ?_
      dsimp only [kyberMapSpec]
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun htr1 => ?_
      refine SepWPp.fold (stackAt_eq_sp hsp1) (by sep_focus) ?_
      refine SepWPp.fold (kyberPost_unpack A (sp + 0x8a0#64) (sp + 0x580#64) 0#64 none) (by sep_focus) ?_
      refine sepWPp_elim_ex fun bp => ?_
      refine SepWPp.fold (kyberArgAt_none_to_memRegion sp) (by sep_focus) ?_
      rcases hcs1 with ⟨hx19_1, hx20_1, _hx21_1, hx22_1, _hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
      simp only [wp_norm, arm64_norm]
        at hx19_1 hx20_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1 hsp1 htr1
      rw [hx19] at hx19_1; rw [hx20] at hx20_1; rw [hx22] at hx22_1
      rw [hx25] at hx25_1; rw [hx26] at hx26_1
      rw [hx28] at hx28_1; rw [hx29] at hx29_1; rw [hvregs] at hvregs_1
      have hx24_1' : (s1.readReg64 .x24).setWidth 32 = (if items.preKeyId.isSome then 1#32 else 0#32) := by
        change (s1.readReg64 (.gpr 24#5)).setWidth 32 = _; rw [hx24_1]; exact hx24
      have hsp1_al : s1.spAligned = true := by
        unfold State.spAligned at hspAl ⊢; rwa [hsp1]
      rw [hsp] at hsp1
      rw [htr] at htr1
      rw [← hGky]
      apply CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.SepWPp.of_sepWP_ret
      refine SepWP.fold (sessionAt_regId_pack A sp G sess taken) (by sep_focus) ?_
      refine SepWP.fold (takenRecord_sessionRecordAt_pack_exact A sp prevCap prevPtr G sess taken)
        (by sep_focus) ?_
      refine SepWP.fold (preKeyEncryptScratch_pack sp kyLen _ sess.localRegistrationId items.signedPreKeyId pkVal)
        (by sep_focus) ?_
      refine SepWP.fold (pollPreKeyEncrypt_pack A sp bp items sess.pendingKyberPreKey none (by simp [hky]))
        (by sep_focus) ?_
      have hsp1_pack :
          (memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - (allocHookStack + 0x40)) ∗
            stackAt s1.sp (allocHookStack + 0x40)) ⊢ stackAt sp encSubStack := by
        rw [hsp1, ← encSubStack_split_kyber rfl]
        exact Entails.refl _
      refine SepWP.fold hsp1_pack (by sep_focus) ?_
      apply SepWP.done hpc1 hstat1
      intro hcrl_f hmf
      dsimp only [PreKeyEncryptStatePlaced, PreKeyEncryptState'Placed, preKeyEncryptScratch,
        preKeyEncryptScratch', pollPreKeyEncrypt, pollE6c', encMidMetaPlaced, encEntryPlaced,
        encSpillsAt, encSpillsAtV, encCommonPlaced, nowAt, lsLogOff_eq, sp]
        at hsp1 hx19_1 hx20_1 hx22_1 hx24_1' hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1 hmf ⊢
      refine ⟨prevCap, prevPtr, G, ts, expiry, pkVal, bp, hts, hexp, hlt, hpkVal,
        hpc1,
        ⟨hstat1, hsp1, hsp0Al, hsp1_al, hx29_1, hx19_1, hcrl_f, hvregs_1⟩,
        htr1, hx20_1, hx22_1, hx24_1', hx25_1, hx26_1, hx27_1, hx28_1,
        hptlen, hrestlen, hlocA, hnow, hstack, ?_⟩
      arm64_sep_close
  | some ky =>
    cases hGky : G.kyber with
    | none =>
      rw [hGky, hky] at hkyRel
      exact False.elim hkyRel
    | some g =>
      rw [hGky, hky] at hkyRel
      dsimp only [KyberRel] at hkyRel
      rcases hkyRel with ⟨hkyBytes, _⟩
      rw [hGky] at hkySlice
      dsimp only [unackKyberSliceProp] at hkySlice
      rcases hkySlice with ⟨rfl, rfl⟩
      have hkyId_eq : kyIdVal = ky.preKeyId := hkyIdVal ky.preKeyId (by simp [hky])
      subst hkyId_eq
      have hct_lt : ky.ciphertext.length < 2 ^ 32 := hky_bound ky hky
      rw [hkyBytes]
      refine SepWPp.fold (optTailVecAt_borrow A (sp + 0x250#64) g) (by sep_focus) ?_
      rw [sepConj_assoc, sepConj_assoc]
      refine SepWPp.pure_elim fun hptr => ?_
      rw [hkyBytes]
      dsimp only [Option.map, Option.isSome]
      have hptr_beq : (g.vec.ptr == 0#64) = false := _root_.beq_false_of_ne hptr
      apply StoreKit.sepWPp_seq_lscro hcrl (mid := lsmpl.base 430)
      wp_steps
      refine SepWP.fold (kyberArgAt_some_pack sp g.vec.ptr ky hptr hct_lt) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hcrl_call
      refine SepWPp.call_frame_rocl hkyber_call
        (x := ⟨sp + 0x8a0#64, sp + 0x580#64, g.vec.ptr,
          some (⟨ky.preKeyId, ky.ciphertext⟩ : KyberPayload)⟩)
        (by wp_norm_goal) (by wp_norm_goal)
        (by dsimp [State.spAligned, State.sp, State.setPC, State.setMem, State.setPState, State.writeReg64, State.readReg64]; exact hspAl)
        (show _ = (blkPl_464).base + 2228#64 by wp_norm_goal)
        hcrl_call
        rfl ⟨by wp_norm_goal, by wp_norm_goal⟩
        (by dsimp [State.sp, State.setPC, State.setMem, State.setPState, State.writeReg64, State.readReg64]; sep_focus)
        (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
        (fun sf _ hm => by
          rw [sepConj_assoc] at hm
          refine onPanic_of_alloc_placed (s := _) ?_ hm
          change s0.trace <+: s.trace
          rw [htr]
          exact ⟨kit.loadEvs encRecord x.rem.val (.ok (some r)), rfl⟩)
        fun s1 hpc1 hstat1 hsp1 hcs1 _hcrl1 => ?_
      dsimp only [kyberMapSpec]
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun htr1 => ?_
      refine SepWPp.fold (stackAt_eq_sp hsp1) (by sep_focus) ?_
      refine SepWPp.fold
        (kyberPost_unpack A (sp + 0x8a0#64) (sp + 0x580#64) g.vec.ptr
          (some (⟨ky.preKeyId, ky.ciphertext⟩ : KyberPayload)))
        (by sep_focus) ?_
      refine sepWPp_elim_ex fun bp => ?_
      refine SepWPp.fold (kyberArgAt_some_unpack sp g.vec.ptr ky) (by sep_focus) ?_
      rw [← hkyBytes]
      refine SepWPp.fold (optTailVecAt_unborrow A (sp + 0x250#64) g) (by sep_focus) ?_
      rw [hkyBytes, ← hGky]
      rcases hcs1 with ⟨hx19_1, hx20_1, _hx21_1, hx22_1, _hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
      simp only [wp_norm, arm64_norm]
        at hx19_1 hx20_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1 hsp1 htr1
      rw [hx19] at hx19_1; rw [hx20] at hx20_1; rw [hx22] at hx22_1
      rw [hx25] at hx25_1; rw [hx26] at hx26_1
      rw [hx28] at hx28_1; rw [hx29] at hx29_1; rw [hvregs] at hvregs_1
      have hx24_1' : (s1.readReg64 .x24).setWidth 32 = (if items.preKeyId.isSome then 1#32 else 0#32) := by
        change (s1.readReg64 (.gpr 24#5)).setWidth 32 = _; rw [hx24_1]; exact hx24
      have hsp1_al : s1.spAligned = true := by
        unfold State.spAligned at hspAl ⊢; rwa [hsp1]
      rw [hsp] at hsp1
      rw [htr] at htr1
      apply CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.SepWPp.of_sepWP_ret
      refine SepWP.fold (sessionAt_regId_pack A sp G sess taken) (by sep_focus) ?_
      refine SepWP.fold (takenRecord_sessionRecordAt_pack_exact A sp prevCap prevPtr G sess taken)
        (by sep_focus) ?_
      refine SepWP.fold (preKeyEncryptScratch_pack sp _ _ sess.localRegistrationId items.signedPreKeyId pkVal)
        (by sep_focus) ?_
      refine SepWP.fold
        (pollPreKeyEncrypt_pack A sp bp items sess.pendingKyberPreKey
          (some (⟨ky.preKeyId, ky.ciphertext⟩ : KyberPayload)) (by simp [hky]))
        (by sep_focus) ?_
      have hsp1_pack :
          (memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - (allocHookStack + 0x40)) ∗
            stackAt s1.sp (allocHookStack + 0x40)) ⊢ stackAt sp encSubStack := by
        rw [hsp1, ← encSubStack_split_kyber rfl]
        exact Entails.refl _
      refine SepWP.fold hsp1_pack (by sep_focus) ?_
      apply SepWP.done hpc1 hstat1
      intro hcrl_f hmf
      dsimp only [PreKeyEncryptStatePlaced, PreKeyEncryptState'Placed, preKeyEncryptScratch,
        preKeyEncryptScratch', pollPreKeyEncrypt, pollE6c', encMidMetaPlaced, encEntryPlaced,
        encSpillsAt, encSpillsAtV, encCommonPlaced, nowAt, lsLogOff_eq, sp]
        at hsp1 hx19_1 hx20_1 hx22_1 hx24_1' hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1 hmf ⊢
      refine ⟨prevCap, prevPtr, G, ts, expiry, pkVal, bp, hts, hexp, hlt, hpkVal,
        hpc1,
        ⟨hstat1, hsp1, hsp0Al, hsp1_al, hx29_1, hx19_1, hcrl_f, hvregs_1⟩,
        htr1, hx20_1, hx22_1, hx24_1', hx25_1, hx26_1, hx27_1, hx28_1,
        hptlen, hrestlen, hlocA, hnow, hstack, ?_⟩
      arm64_sep_close

/-! ## 2. Top-Level `segPreKey_placed_okV` Composition -/

theorem segPreKey_placed_okV [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks} :
    SegPreKeySpecVPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord Hk := by
  intro env x r sess otr taken pqCap pqPtr k R s0 s his hkey
  obtain ⟨items, hpk⟩ := Option.isSome_iff_exists.mp his
  have hcur := hkey.1
  have hscope := hkey.2.1
  have hfrom := hkey.2.2.1
  have hrem := hkey.2.2.2.1
  refine segExitPlaced_trans
    (segPreKey_unackItems_to_dur_placed_ok env x r sess otr taken pqCap pqPtr k items R s0 s hpk hkey) ?_
  rintro s1 ⟨prevCap, prevPtr, G, ts, pkVal, kyIdVal, kyPtr, kyLen, hdur⟩
  refine segExitPlaced_trans
    (segPreKey_staleness_to_add_placed_ok env x r sess otr taken pqCap pqPtr k items
      prevCap prevPtr G ts pkVal kyIdVal kyPtr kyLen R s0 s1
      hcur hscope hfrom hrem hpk hdur) ?_
  rintro s2 ⟨expiry, hadd⟩
  by_cases hlt : expiry.lt x.now = true
  · exact Pf.SegFrom.SegExitPlaced.of_false (segPreKey_stale_placed_ok env x r sess otr taken pqCap pqPtr k items
      prevCap prevPtr G ts expiry pkVal kyIdVal kyPtr kyLen R s0 s2
      hcur hscope hfrom hrem hpk hlt hadd)
  · have hlt_f : expiry.lt x.now = false := Bool.eq_false_iff.mpr hlt
    refine segExitPlaced_trans
      (segPreKey_regId_kyber_placed_ok env x r sess otr taken pqCap pqPtr k items
        prevCap prevPtr G ts expiry pkVal kyIdVal kyPtr kyLen R s0 s2
        hcur hscope hlt_f hadd) ?_
    intro s3 he6c
    exact segPreKey_tail_placed_ok env x r sess otr taken pqCap pqPtr k items R s0 s3
      hcur hscope hfrom hrem hpk he6c

end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey

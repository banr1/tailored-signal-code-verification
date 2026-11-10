/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadShimPollPlaced
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegLoadDispatch
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs

/-!
# Relocatable CLI `SegLoad` Dispatch: `.error ()` & `.ok none` Branches

Proves `segLoad_dispatch_err_placed` (`ans = .error ()` → `+0x5b4`) and
`segLoad_dispatch_none_placed` (`ans = .ok none` → `+0x5b4`) on `lsProg_464 Hk` (`blkPl_464`)
under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.CliRatchet.EncPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  LibsignalCodeRoLoaded withLsCodeRoLoaded sepWP_seq_lscro sepWPp_seq_lscro
open CryptoVerification.LibsignalTripleRatchet.RawByteMove CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Placed Frame Helpers for Load-Error Exits -/

theorem loadOutResPlaced_err_eq (Scope : SessionRecord (List (BitVec 8)) → Prop) (A : RustAlloc)
    (w0 w1 w2 w3 w4 w5 w6 : BitVec 64) (tail : List (BitVec 8)) :
    LoadOutResPlaced Scope A (.error ()) w0 w1 w2 w3 w4 w5 w6 tail =
      ∃∗ strPtr : BitVec 64, ∃∗ vt : BitVec 64,
        ⌜w0 = 0xFFFFFFFFFFFFFFFE#64 ∧ w1 = 0x800000000000001A#64 ∧
          w2 = strPtr ∧ w3 = 10#64 ∧ w4 = 1#64 ∧ w5 = vt⌝ ∗
          (strPtr ↦ᵣ storeHookStr) := rfl

theorem dispatchFramePlaced_tail_entails [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (s0 : State) (v50 : BitVec 64) :
    protocolAddressAt A x.rem x.remA ∗ A.pool ∗ stackAt (s0.sp - 0xbe0#64) encSubStack ∗
      dispatchFramePlaced kit st0 ikit ist0 ctl x s0 v50 ⊢
    memRegion (s0.sp - 0xbe0#64) 0x58 ∗ memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x35a ∗
      memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗ memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
      encSpillsAtV kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗ memRegion x.ret 248 ∗
      encCommonPlaced A ctl x 0 s0 ∗ encStoreExtraPlaced kit st0 ikit ist0 x s0 := by
  dsimp only [dispatchFramePlaced, encCommonPlaced]
  have hspills := encSpillsAt_fold kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x
  have h58 := fold_sp58 (s0.sp - 0xbe0#64) v50
  have h35a := memRegion_0x110_0x35a_fold (s0.sp - 0xbe0#64) 0#8 0#8
  have hperm :
      protocolAddressAt A x.rem x.remA ∗ A.pool ∗ stackAt (s0.sp - 0xbe0#64) encSubStack ∗
        (nowAt s0.sp x.now ∗ encSavedRegs s0.sp s0 ∗ memRegion (s0.sp - 0xbe0#64) 0x50 ∗
          ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ v50) ∗ encSpillsInit kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
          ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗ memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x358 ∗
          ((s0.sp - 0xbe0#64 + 0x468#64) ↦₈ 0#8) ∗ ((s0.sp - 0xbe0#64 + 0x469#64) ↦₈ 0#8) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗ memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
          (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.loc x.locA ∗
          memRegion x.ret 248 ∗ cliTapeAfter ctl x.cur x.rest 0 ∗ FromRecordCallees.lsLogOff ∗
          encStoreExtraPlaced kit st0 ikit ist0 x s0) =
      (memRegion (s0.sp - 0xbe0#64) 0x50 ∗ ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ v50)) ∗
      (memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x358 ∗ ((s0.sp - 0xbe0#64 + 0x468#64) ↦₈ 0#8) ∗
        ((s0.sp - 0xbe0#64 + 0x469#64) ↦₈ 0#8)) ∗
      memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗ memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
      (encSpillsInit kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗ ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA)) ∗
      memRegion x.ret 248 ∗
      ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest 0 ∗ FromRecordCallees.lsLogOff ∗
        stackAt (s0.sp - 0xbe0#64) encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool) ∗
      encStoreExtraPlaced kit st0 ikit ist0 x s0 := by
    sep_ac_rfl
  rw [hperm]
  exact sepConj_mono h58 (sepConj_mono h35a (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left hspills))))

/-! ## 2. Branch 1: `ans = .error ()` (`+0x160..+0x174` → `+0x5b4` `tailWriteErr_placed_ok`) -/

theorem segLoad_dispatch_err_placed_wp [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (_env : EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord Hk)
    {s : State} {sp w4 w5 w6 : BitVec 64} {F : SepProp}
    (hpc : s.pc = encEntryPlaced + 0x160#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hps : s.pstate = addsPState64 0xFFFFFFFFFFFFFFFE#64 2#64) :
    SepWP (lsProg_464 Hk) (encEntryPlaced + 0x5b4#64) s
      (((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗ ((sp + 0x840#64) ↦₆₄ w6) ∗
        memRegion (sp + 0x848#64) 0x338 ∗ F)
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        sf.readReg64 .x26 = sp + 0x9d0#64 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        P_f = (((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗ ((sp + 0x840#64) ↦₆₄ w6) ∗
          memRegion (sp + 0x848#64) 0x188 ∗
          ((sp + 0x9d0#64) ↦₆₄ w4) ∗ ((sp + 0x9d8#64) ↦₆₄ w5) ∗ ((sp + 0x9e0#64) ↦₆₄ w6) ∗
          memRegion (sp + 0x9e8#64) 0x198 ∗ F)) := by
  subst hsp
  have hal_norm : (s.sp &&& 15#64 == 0#64) = true := hal
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true] at hpc ⊢
  simp only [wp_norm, arm64_norm] at hx25 hx26
  wp_conv_pre => rw [memRegion_0x848_split_0x9d0 s.sp]
  wp_simp_pre [cells_succ, cells_zero, sepConj_emp,
    sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    sepConj_assoc]
  apply SepWP.exists_elim; intro _
  apply SepWP.exists_elim; intro _
  apply SepWP.exists_elim; intro _
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  simp only [wp_norm, arm64_norm, hx26, hal_norm, true_and]

set_option maxHeartbeats 800000 in
theorem segLoad_dispatch_err_placed [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (env : EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord Hk)
    (x : WithStoresEncGhost) (R : SepProp) (s0 s : State)
    (sp w0 w1 w2 w3 w4 w5 w6 v50 : BitVec 64) (tail : List (BitVec 8))
    (hsp_eq : sp = s0.sp - 0xbe0#64)
    (hpc : s.pc = encEntryPlaced + 0x160#64)
    (hmeta : encMidMetaPlaced x s0 s)
    (hsp_le : withStoresEncStackV kit ikit ≤ s0.sp.toNat)
    (htail : tail.length = 312)
    (hl : kit.loadRel st0 x.rem.val (.error ()))
    (htr : s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.error ()))
    (hx27 : s.readReg64 .x27 = w1) (hx21 : s.readReg64 .x21 = w2) (hx23 : s.readReg64 .x23 = w3)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64)
    (hps : s.pstate = addsPState64 w0 2#64)
    (hm : s.mem ⊨ (memRegion (sp + 0x46a#64) 0x116 ∗
      memRegion (sp + 0x580#64) 368 ∗
      ((sp + 0x6f8#64) ↦ₛ tail) ∗
      ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗
      ((sp + 0x840#64) ↦₆₄ w6) ∗
      LoadOutResPlaced Scope A (.error ()) w0 w1 w2 w3 w4 w5 w6 tail ∗
      protocolAddressAt A x.rem x.remA ∗
      A.pool ∗ stackAt sp encSubStack ∗ loadVtablesAt kit ∗
      dispatchFramePlaced kit st0 ikit ist0 ctl x s0 v50) ∗ R) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s
      (fun s' => ∃ r g sess,
        CurStateVPlaced kit st0 ikit ist0 Scope ctl encRecord x r g sess R s0 s') := by
  subst hsp_eq
  rcases hmeta with ⟨hrun, hsp, hal0, hal, hx29, hx19, hcrl, hvregs⟩
  have hm_drop : s.mem ⊨
      LoadOutResPlaced Scope A (.error ()) w0 w1 w2 w3 w4 w5 w6 tail ∗
      ((memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
        ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
        ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
        ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
        protocolAddressAt A x.rem x.remA ∗
        A.pool ∗ stackAt (s0.sp - 0xbe0#64) encSubStack ∗
        dispatchFramePlaced kit st0 ikit ist0 ctl x s0 v50) ∗ R) := by
    refine Satisfies.drop_left (P := loadVtablesAt kit) ?_
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  clear hm
  rw [loadOutResPlaced_err_eq] at hm_drop
  obtain ⟨strPtr, hm_drop1⟩ := satisfies_sepExists_left hm_drop
  obtain ⟨vt, hm_drop2⟩ := satisfies_sepExists_left hm_drop1
  clear hm_drop hm_drop1
  rw [sepConj_assoc] at hm_drop2
  obtain ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, hm_drop'⟩ := satisfies_pure_left hm_drop2
  let strPtr := w2; let vt := w5
  clear hm_drop2
  rw [← sepConj_assoc] at hm_drop'
  have hm_tail : s.mem ⊨
      (((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ 1#64) ∗
        ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ vt) ∗
        ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
        memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
        ((strPtr ↦ᵣ storeHookStr) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
          ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
          memRegion (s0.sp - 0xbe0#64) 0x58 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x35a ∗
          encSpillsAtV kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
          memRegion x.ret 248 ∗
          encCommonPlaced A ctl x 0 s0 ∗
          encStoreExtraPlaced kit st0 ikit ist0 x s0)) ∗ R := by
    refine Satisfies.mono ?_ hm_drop'
    refine sepConj_mono_left ?_
    have hfr := dispatchFramePlaced_tail_entails kit st0 ikit ist0 ctl x s0 v50
    have hperm1 :
        (strPtr ↦ᵣ storeHookStr) ∗
          (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
          ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
          ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ 1#64) ∗
          ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ vt) ∗
          ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
          protocolAddressAt A x.rem x.remA ∗
          A.pool ∗ stackAt (s0.sp - 0xbe0#64) encSubStack ∗
          dispatchFramePlaced kit st0 ikit ist0 ctl x s0 v50) =
        (protocolAddressAt A x.rem x.remA ∗ A.pool ∗ stackAt (s0.sp - 0xbe0#64) encSubStack ∗
          dispatchFramePlaced kit st0 ikit ist0 ctl x s0 v50) ∗
        ((strPtr ↦ᵣ storeHookStr) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
          ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
          ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ 1#64) ∗
          ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ vt) ∗
          ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6)) := by
      sep_ac_rfl
    rw [hperm1]
    refine Entails.trans (sepConj_mono_left hfr) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  have hwp := segLoad_dispatch_err_placed_wp env
    (w4 := 1#64) (w5 := vt) (w6 := w6)
    (F := (strPtr ↦ᵣ storeHookStr) ∗
      memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
      ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
      memRegion (s0.sp - 0xbe0#64) 0x58 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x35a ∗
      encSpillsAtV kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
      memRegion x.ret 248 ∗
      encCommonPlaced A ctl x 0 s0 ∗
      encStoreExtraPlaced kit st0 ikit ist0 x s0)
    hpc hrun hsp hal hx25 hx26 hps
  refine segExit_placed_of_sepWP_frozen hcrl hm_tail hwp ?_
  intro sf P_f hpcf hrunf hpostf hcrlf hm_f
  rcases hpostf with ⟨hspf, half, htrf, hx19f, hx29f, hvregsf, hx26f, hx28f, hx27f, hx21f, hx23f, rfl⟩
  refine segExit_placed_of_false (tailWriteErr_placed_ok env x R s0 sf (answersOfLoad (.error ())) (.store ())
    0x800000000000001A#64 strPtr 10#64 1#64 vt w6
    (strPtr ↦ᵣ storeHookStr)
    (tailModel_load_err hl (htrf.trans htr))
    (speStaged_storeErr_placed A x.ret strPtr vt w6)
    ⟨hpcf, ⟨hrunf, hspf, hal0, half, hx29f.trans hx29, hx19f.trans hx19, hcrlf, hvregsf.trans hvregs⟩,
      ⟨hx26f, hx28f.trans hx28, hx27f.trans hx27, hx21f.trans hx21, hx23f.trans hx23⟩,
      enc_sp_bound_of_kit kit ikit hsp_le, ?_⟩)
  dsimp only [EncTailVPlaced, Pf.TailCommon.EncTailVPlaced]
  rw [draws_answersOfLoad_err]
  change sf.mem ⊨ _ ∗ _ ∗ _ ∗ _ ∗ (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R)
  refine Satisfies.mono ?_ hm_f
  have hpoll := pollWith_0x9d0_fold (s0.sp - 0xbe0#64)
    1#64 vt w6 1#64 vt w6 tail htail
  have hperm2 :
      ((((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ 1#64) ∗
        ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ vt) ∗
        ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
        memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x188 ∗
        ((s0.sp - 0xbe0#64 + 0x9d0#64) ↦₆₄ 1#64) ∗
        ((s0.sp - 0xbe0#64 + 0x9d8#64) ↦₆₄ vt) ∗
        ((s0.sp - 0xbe0#64 + 0x9e0#64) ↦₆₄ w6) ∗
        memRegion (s0.sp - 0xbe0#64 + 0x9e8#64) 0x198 ∗
        ((strPtr ↦ᵣ storeHookStr) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
          ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
          memRegion (s0.sp - 0xbe0#64) 0x58 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x35a ∗
          encSpillsAtV kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
          memRegion x.ret 248 ∗
          encCommonPlaced A ctl x 0 s0 ∗
          encStoreExtraPlaced kit st0 ikit ist0 x s0)) ∗ R) =
      ((memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
        ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
        ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ 1#64) ∗
        ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ vt) ∗
        ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
        memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x188) ∗
      (((s0.sp - 0xbe0#64 + 0x9d0#64) ↦₆₄ 1#64) ∗
        ((s0.sp - 0xbe0#64 + 0x9d8#64) ↦₆₄ vt) ∗
        ((s0.sp - 0xbe0#64 + 0x9e0#64) ↦₆₄ w6)) ∗
      memRegion (s0.sp - 0xbe0#64 + 0x9e8#64) 0x198) ∗
      (memRegion (s0.sp - 0xbe0#64) 0x58 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x35a ∗
        (strPtr ↦ᵣ storeHookStr) ∗
        encSpillsAtV kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
        memRegion x.ret 248 ∗
        encCommonPlaced A ctl x 0 s0 ∗
        (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R)) := by
    sep_ac_rfl
  rw [hperm2]
  refine Entails.trans (sepConj_mono_left hpoll) ?_
  exact Entails.of_eq (by sep_ac_rfl)

/-! ## 3. Branch 2: `ans = .ok none` (`+0x160`, `+0x178..+0x180`, `+0x41c..+0x458` → `+0x5b4`) -/

theorem loadOutResPlaced_none_eq (Scope : SessionRecord (List (BitVec 8)) → Prop) (A : RustAlloc)
    (w0 w1 w2 w3 w4 w5 w6 : BitVec 64) (tail : List (BitVec 8)) :
    LoadOutResPlaced Scope A (.ok none) w0 w1 w2 w3 w4 w5 w6 tail =
      ⌜w0 = 0xFFFFFFFFFFFFFFFF#64⌝ := rfl

def dispatchFrameNo108848Placed [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64)
    (st0 : kit.StoreState) (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (ctl : BitVec 64)
    (x : WithStoresEncGhost) (s0 : State) (v50 : BitVec 64) : SepProp :=
  let sp := s0.sp - 0xbe0#64
  nowAt s0.sp x.now ∗
  encSavedRegs s0.sp s0 ∗
  memRegion sp 0x50 ∗
  ((sp + 0x50#64) ↦₆₄ v50) ∗
  encSpillsInit kit.ss_vt ikit.id_vt sp x ∗
  memRegion (sp + 0x110#64) 0x358 ∗
  ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
  memRegion (sp + 0x6f0#64) 8 ∗
  (x.ptA ↦ₛ x.ptext) ∗
  protocolAddressAt A x.loc x.locA ∗
  memRegion x.ret 248 ∗
  cliTapeAfter ctl x.cur x.rest 0 ∗
  FromRecordCallees.lsLogOff ∗
  encStoreExtraPlaced kit st0 ikit ist0 x s0

theorem dispatchFramePlaced_eq_108_848_sep [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (s0 : State) (v50 : BitVec 64) :
    dispatchFramePlaced kit st0 ikit ist0 ctl x s0 v50 =
      ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
      memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
      dispatchFrameNo108848Placed kit st0 ikit ist0 ctl x s0 v50 := by
  dsimp only [dispatchFramePlaced, dispatchFrameNo108848Placed]
  sep_ac_rfl

theorem segLoad_dispatch_none_pre_placed_wp [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (_env : EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord Hk)
    {s : State} {sp remA : BitVec 64} {F : SepProp}
    (hpc : s.pc = encEntryPlaced + 0x160#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true)
    (hx24 : s.readReg64 .x24 = 0xFFFFFFFFFFFFFFFF#64)
    (hps : s.pstate = addsPState64 0xFFFFFFFFFFFFFFFF#64 2#64) :
    SepWP (lsProg_464 Hk) (lsmpl.base 623) s
      (((sp + 0x108#64) ↦₆₄ remA) ∗ F)
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = remA ∧
        sf.readReg64 .x8 = sp + 0x580#64 ∧
        sf.readReg64 .x22 = remA ∧
        sf.readReg64 .x30 = encEntryPlaced + 0x428#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        P_f = (((sp + 0x108#64) ↦₆₄ remA) ∗ F)) := by
  subst hsp
  have hal_norm : (s.sp &&& 15#64 == 0#64) = true := hal
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true] at hpc ⊢
  simp only [wp_norm, arm64_norm] at hx24
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  simp only [wp_norm, arm64_norm, hal_norm, true_and]

set_option maxHeartbeats 800000 in
theorem segLoad_dispatch_none_post_placed_wp [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (_env : EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord Hk)
    {s : State} {sp remA cap ptr len : BitVec 64} {dev : BitVec 8} {F : SepProp}
    (hpc : s.pc = encEntryPlaced + 0x428#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true)
    (hx22 : s.readReg64 .x22 = remA)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64) :
    SepWP (lsProg_464 Hk) (encEntryPlaced + 0x5b4#64) s
      (((remA + 0x18#64) ↦₈ dev) ∗
        ((sp + 0x580#64) ↦₆₄ cap) ∗ ((sp + 0x588#64) ↦₆₄ ptr) ∗
        ((sp + 0x590#64) ↦₆₄ len) ∗
        memRegion (sp + 0x598#64) 344 ∗
        memRegion (sp + 0x848#64) 0x338 ∗ F)
      (fun sf P_f =>
        ∃ w3 : BitVec 64, DevWord dev w3 ∧
          sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
          sf.readReg64 .x19 = s.readReg64 .x19 ∧
          sf.readReg64 .x29 = s.readReg64 .x29 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          sf.readReg64 .x26 = sp + 0x9d0#64 ∧
          sf.readReg64 .x28 = sp + 0x4a0#64 ∧
          sf.readReg64 .x27 = cap ∧
          sf.readReg64 .x21 = ptr ∧
          sf.readReg64 .x23 = len ∧
          P_f = (((remA + 0x18#64) ↦₈ dev) ∗
            memRegion (sp + 0x580#64) 368 ∗
            memRegion (sp + 0x848#64) 0x188 ∗
            ((sp + 0x9d0#64) ↦₆₄ w3) ∗
            ((sp + 0x9d8#64) ↦₆₄ (lsmpl.ρ "libsignal_cli_ratchet:.rodata..Lanon.122")) ∗
            ((sp + 0x9e0#64) ↦₆₄ 15#64) ∗
            memRegion (sp + 0x9e8#64) 0x198 ∗ F)) := by
  subst hsp
  have hal_norm : (s.sp &&& 15#64 == 0#64) = true := hal
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true] at hpc ⊢
  simp only [wp_norm, arm64_norm] at hx22 hx26 hx28
  wp_conv_pre =>
    rw [memRegion_0x598_split s.sp, memRegion_0x848_split_0x9d0 s.sp]
  wp_simp_pre [cells_succ, cells_zero, sepConj_emp,
    sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    sepConj_assoc]
  repeat (apply SepWP.exists_elim; intro _)
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  apply SepWP.fold (devWord_of_pointsTo8_memRegion7_1432 s.sp dev) (by sep_focus)
  wp_simp_pre [sepExists_sepConj_left, sepConj_assoc]
  apply SepWP.exists_elim; intro w3
  apply SepWP.pure_elim; intro hdev
  wp_steps
  apply SepWP.fold (memRegion_0x580_368_fold s.sp cap ptr len w3 _) (by sep_focus)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨w3, hdev, ?_⟩
  simp only [wp_norm, arm64_norm, hx26, hx28, hal_norm, true_and]
  sep_ac_rfl

set_option maxHeartbeats 800000 in
theorem segLoad_dispatch_none_placed [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (env : EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord Hk)
    (x : WithStoresEncGhost) (R : SepProp) (s0 s : State)
    (sp w0 w1 w2 w3 w4 w5 w6 v50 : BitVec 64) (tail : List (BitVec 8))
    (hsp_eq : sp = s0.sp - 0xbe0#64)
    (hpc : s.pc = encEntryPlaced + 0x160#64)
    (hmeta : encMidMetaPlaced x s0 s)
    (hsp_le : withStoresEncStackV kit ikit ≤ s0.sp.toNat)
    (htail : tail.length = 312)
    (hl : kit.loadRel st0 x.rem.val (.ok none))
    (htr : s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok none))
    (hx24 : s.readReg64 .x24 = w0)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64)
    (hps : s.pstate = addsPState64 w0 2#64)
    (hm : s.mem ⊨ (memRegion (sp + 0x46a#64) 0x116 ∗
      memRegion (sp + 0x580#64) 368 ∗
      ((sp + 0x6f8#64) ↦ₛ tail) ∗
      ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗
      ((sp + 0x840#64) ↦₆₄ w6) ∗
      LoadOutResPlaced Scope A (.ok none) w0 w1 w2 w3 w4 w5 w6 tail ∗
      protocolAddressAt A x.rem x.remA ∗
      A.pool ∗ stackAt sp encSubStack ∗ loadVtablesAt kit ∗
      dispatchFramePlaced kit st0 ikit ist0 ctl x s0 v50) ∗ R) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s
      (fun s' => ∃ r g sess,
        CurStateVPlaced kit st0 ikit ist0 Scope ctl encRecord x r g sess R s0 s') := by
  subst hsp_eq
  rcases hmeta with ⟨hrun, hsp, hal0, hal, hx29, hx19, hcrl, hvregs⟩
  have hm_drop : s.mem ⊨
      LoadOutResPlaced Scope A (.ok none) w0 w1 w2 w3 w4 w5 w6 tail ∗
      ((((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
        (vecGhostAt A x.rem.name x.remA ∗
          ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
          memRegion (x.remA + 0x19#64) 7 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 24 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x598#64) 344 ∗
          A.pool ∗
          memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
          stackAt (s0.sp - 0xbe0#64) extHookStack ∗
          memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
          (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
            ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
            ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
            ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
            dispatchFrameNo108848Placed kit st0 ikit ist0 ctl x s0 v50))) ∗ R) := by
    refine Satisfies.drop_left (P := loadVtablesAt kit) ?_
    refine Satisfies.mono ?_ hm
    rw [protocolAddressAt, memRegion_0x580_split_24 (s0.sp - 0xbe0#64),
        stack_encSub_extHook (s0.sp - 0xbe0#64),
        dispatchFramePlaced_eq_108_848_sep kit st0 ikit ist0 ctl x s0 v50]
    exact Entails.of_eq (by sep_ac_rfl)
  clear hm
  rw [loadOutResPlaced_none_eq] at hm_drop
  obtain ⟨rfl, hm_drop'⟩ := satisfies_pure_left hm_drop
  clear hm_drop
  refine segExit_placed_of_sepWPp (target := encEntryPlaced + 0x5b4#64) hm_drop' ?_
  have hpre_wp := segLoad_dispatch_none_pre_placed_wp env
    (remA := x.remA)
    (F := vecGhostAt A x.rem.name x.remA ∗
      ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
      memRegion (x.remA + 0x19#64) 7 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x580#64) 24 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x598#64) 344 ∗
      A.pool ∗
      memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
      stackAt (s0.sp - 0xbe0#64) extHookStack ∗
      memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
      (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
        ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
        ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
        ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
        dispatchFrameNo108848Placed kit st0 ikit ist0 ctl x s0 v50))
    hpc hrun hsp hal hx24 hps
  refine messageEncrypt_of_sepWP_placed hcrl (SepWP.mono hpre_wp ?_)
  intro sm P_m hpcm hrunm hpostm hcrlm
  rcases hpostm with ⟨hspm, halm, htrm, hx0m, hx8m, hx22m, hx30m, hx19m, hx29m, hvregsm, hx26m, hx28m, rfl⟩
  refine messageEncrypt_call_panic_then_wp_placed (stringClone_placed_ok env)
    (x := (x.remA, s0.sp - 0xbe0#64 + 0x580#64, x.rem.name))
    (F := ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
      ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
      memRegion (x.remA + 0x19#64) 7 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x598#64) 344 ∗
      memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
      memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
      (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
        ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
        ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
        ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
        dispatchFrameNo108848Placed kit st0 ikit ist0 ctl x s0 v50))
    hcrlm hpcm hrunm halm hx30m ?_ ?_ (fun _ _ => rfl) ?_
  · intro R' hm'
    dsimp only [CryptoVerification.withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrlm.1, ?_⟩
    dsimp only [stringCloneSpec]
    refine Satisfies.mono ?_ hm'
    rw [hspm]
    have hperm_c :
        (((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
          (vecGhostAt A x.rem.name x.remA ∗
            ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
            memRegion (x.remA + 0x19#64) 7 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x580#64) 24 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x598#64) 344 ∗
            A.pool ∗
            memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
            stackAt (s0.sp - 0xbe0#64) extHookStack ∗
            memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
            (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
              ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
              ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
              ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
              dispatchFrameNo108848Placed kit st0 ikit ist0 ctl x s0 v50))) ∗ R' =
        (vecGhostAt A x.rem.name x.remA ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 24 ∗
          A.pool ∗
          stackAt (s0.sp - 0xbe0#64) extHookStack) ∗
        ((((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
          ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
          memRegion (x.remA + 0x19#64) 7 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x598#64) 344 ∗
          memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
          (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
            ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
            ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
            ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
            dispatchFrameNo108848Placed kit st0 ikit ist0 ctl x s0 v50)) ∗ R') := by
      sep_ac_rfl
    rw [hperm_c]
    apply sepConj_mono_left
    exact Entails.pure_right (And.intro hx0m hx8m) (Entails.refl _)
  · intro sf_p
    dsimp only [CryptoVerification.withLsCodeLoaded, stringCloneSpec]
    exact alloc_onPanic_placed_entails (by rw [htrm, htr]; exact ⟨kit.loadEvs encRecord x.rem.val (.ok none), rfl⟩)
  · intro sf1 hpc1 hrun1 hsp1 hcs1
    rcases hcs1 with ⟨hcs19, _, _, hcs22, _, _, _, hcs26, _, hcs28, hcs29, hcsv1⟩
    dsimp only [CryptoVerification.withLsCodeLoaded, stringCloneSpec]
    wp_conv_pre => rw [vecU8_eq_words3_sep_buf]
    wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_assoc]
    apply SepWP.exists_elim; intro cap
    apply SepWP.exists_elim; intro ptr
    apply SepWP.pure_elim; intro htr1
    have hsp1' : sf1.sp = s0.sp - 0xbe0#64 := by rw [hsp1, hspm]
    have hal1 : sf1.spAligned = true := by rw [State.spAligned, hsp1, ← State.spAligned]; exact halm
    have hx22_1 : sf1.readReg64 .x22 = x.remA := by rw [hcs22, hx22m]
    have hx26_1 : sf1.readReg64 .x26 = s0.sp - 0xbe0#64 + 0x9d0#64 := by rw [hcs26, hx26m, hx26]
    have hx28_1 : sf1.readReg64 .x28 = s0.sp - 0xbe0#64 + 0x4a0#64 := by rw [hcs28, hx28m, hx28]
    have hpost_wp := segLoad_dispatch_none_post_placed_wp env
      (s := sf1) (sp := s0.sp - 0xbe0#64) (remA := x.remA)
      (cap := cap) (ptr := ptr) (len := BitVec.ofNat 64 x.rem.name.bytes.length)
      (dev := x.rem.device)
      (F := vecGhostAt A x.rem.name x.remA ∗
        memRegion (x.remA + 0x19#64) 7 ∗
        vecU8Buf A cap ptr x.rem.name.bytes ∗
        A.pool ∗
        stackAt (s0.sp - 0xbe0#64) encSubStack ∗
        ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
        (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
          ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
          ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
          ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
          dispatchFrameNo108848Placed kit st0 ikit ist0 ctl x s0 v50))
      hpc1 hrun1 hsp1' hal1 hx22_1 hx26_1 hx28_1
    have hpre_post_eq :
        vecGhostAt A x.rem.name x.remA ∗
          ((s0.sp - 0xbe0#64 + 0x580#64) ↦₆₄ cap) ∗
          ((s0.sp - 0xbe0#64 + 1416#64) ↦₆₄ ptr) ∗
          ((s0.sp - 0xbe0#64 + 1424#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length) ∗
          vecU8Buf A cap ptr x.rem.name.bytes ∗
          A.pool ∗
          stackAt sm.sp extHookStack ∗
          ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
          ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
          memRegion (x.remA + 0x19#64) 7 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x598#64) 344 ∗
          memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
          ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
          ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
          ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
          dispatchFrameNo108848Placed kit st0 ikit ist0 ctl x s0 v50 =
        ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
          ((s0.sp - 0xbe0#64 + 0x580#64) ↦₆₄ cap) ∗
          ((s0.sp - 0xbe0#64 + 0x588#64) ↦₆₄ ptr) ∗
          ((s0.sp - 0xbe0#64 + 0x590#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x598#64) 344 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
          (vecGhostAt A x.rem.name x.remA ∗
            memRegion (x.remA + 0x19#64) 7 ∗
            vecU8Buf A cap ptr x.rem.name.bytes ∗
            A.pool ∗
            stackAt (s0.sp - 0xbe0#64) encSubStack ∗
            ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
            (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
              ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
              ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
              ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
              dispatchFrameNo108848Placed kit st0 ikit ist0 ctl x s0 v50)) := by
      rw [hspm, ← stack_encSub_extHook_back (s0.sp - 0xbe0#64)]
      sep_ac_rfl
    refine sepWP_conseq_pc_run hpre_post_eq hpost_wp ?_
    intro sf P_f hpcf hrunf hpostf hcrlf hm_f
    rcases hpostf with ⟨w3', hdev, hspf, half, htrf, hx19f, hx29f, hvregsf, hx26f, hx28f, hx27f, hx21f, hx23f, rfl⟩
    have hm_rod := rodata_message_encrypt_placed_intro hcrlf.2 hm_f
    let msgPtr := lsmpl.ρ "libsignal_cli_ratchet:.rodata..Lanon.122"
    refine segExit_placed_of_false (tailWriteErr_placed_ok env x R s0 sf (answersOfLoad (.ok none))
      (.sessionNotFound x.rem.val "message_encrypt")
      cap ptr (BitVec.ofNat 64 x.rem.val.name.length) w3' msgPtr 15#64
      (vecU8Buf A cap ptr x.rem.val.name ∗ (msgPtr ↦ᵣ utf8 "message_encrypt"))
      (tailModel_load_none hl (by rw [htrf, htr1, htrm, htr]))
      (speStaged_sessionNotFound_devWord_placed A x.ret cap ptr w3' msgPtr x.rem.val hdev)
      ⟨hpcf, ⟨hrunf, hspf, hal0, half,
        by rw [hx29f, hcs29, hx29m, hx29],
        by rw [hx19f, hcs19, hx19m, hx19], hcrlf,
        by rw [hvregsf, hcsv1, hvregsm, hvregs]⟩,
        ⟨hx26f, hx28f, hx27f, hx21f, hx23f⟩,
        enc_sp_bound_of_kit kit ikit hsp_le, ?_⟩)
    dsimp only [EncTailVPlaced, Pf.TailCommon.EncTailVPlaced]
    rw [draws_answersOfLoad_none]
    change sf.mem ⊨ _ ∗ _ ∗ _ ∗ _ ∗ (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R)
    refine Satisfies.mono ?_ hm_rod
    have hpoll := pollWith_0x9d0_fold (s0.sp - 0xbe0#64)
      w3' msgPtr 15#64 w4 w5 w6 tail htail
    have hperm_end :
        (msgPtr ↦ᵣ utf8 "message_encrypt") ∗
        ((((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x188 ∗
          ((s0.sp - 0xbe0#64 + 0x9d0#64) ↦₆₄ w3') ∗
          ((s0.sp - 0xbe0#64 + 0x9d8#64) ↦₆₄ msgPtr) ∗
          ((s0.sp - 0xbe0#64 + 0x9e0#64) ↦₆₄ 15#64) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x9e8#64) 0x198 ∗
          (vecGhostAt A x.rem.name x.remA ∗
            memRegion (x.remA + 0x19#64) 7 ∗
            vecU8Buf A cap ptr x.rem.name.bytes ∗
            A.pool ∗
            stackAt (s0.sp - 0xbe0#64) encSubStack ∗
            ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
            (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
              ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
              ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗
              ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
              ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
              dispatchFrameNo108848Placed kit st0 ikit ist0 ctl x s0 v50))) ∗ R) =
        (memRegion (s0.sp - 0xbe0#64) 0x50 ∗ ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ v50)) ∗
        (memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x358 ∗
          ((s0.sp - 0xbe0#64 + 0x468#64) ↦₈ 0#8) ∗ ((s0.sp - 0xbe0#64 + 0x469#64) ↦₈ 0#8)) ∗
        ((memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
          ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
          ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗
          ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
          ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x188) ∗
        (((s0.sp - 0xbe0#64 + 0x9d0#64) ↦₆₄ w3') ∗
          ((s0.sp - 0xbe0#64 + 0x9d8#64) ↦₆₄ msgPtr) ∗
          ((s0.sp - 0xbe0#64 + 0x9e0#64) ↦₆₄ 15#64)) ∗
        memRegion (s0.sp - 0xbe0#64 + 0x9e8#64) 0x198) ∗
        (encSpillsInit kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗ ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA)) ∗
        ((vecU8Buf A cap ptr x.rem.val.name ∗ (msgPtr ↦ᵣ utf8 "message_encrypt")) ∗
          memRegion x.ret 248 ∗
          encCommonPlaced A ctl x 0 s0 ∗
          (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R)) := by
      dsimp only [dispatchFrameNo108848Placed, encCommonPlaced, protocolAddressAt, AddrGhost.val]
      sep_ac_rfl
    rw [hperm_end]
    refine Entails.trans (sepConj_mono (fold_sp58 _ _)
      (sepConj_mono (memRegion_0x110_0x35a_fold _ _ _)
        (sepConj_mono hpoll
          (sepConj_mono_left (encSpillsAt_fold _ _ _ _))))) ?_
    exact Entails.of_eq (by sep_ac_rfl)

end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad

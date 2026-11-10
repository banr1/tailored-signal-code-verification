/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg4Placed
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadDispatchSomePlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalPlaced
public import LibsignalBinary.Proofs.Common.SharedHelpers
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

@[expose] public section

set_option autoImplicit false

/-!
# Relocatable CLI `MessageEncrypt` `WithStoresVT` (Part 5): `SegLoad`
-/

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad
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
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails
open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local wp_norm] spAligned_writeVReg128 loadBoxSize_ofNat_toNat

section SegLoad

private theorem h45_encSubStackV_kitL {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64) :
    encSubStackV (h45_kitL_placed kit) ikit = encSubStackV kit ikit := rfl

private theorem h45_loadVtablesAt_kitL {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) :
    loadVtablesAt (h45_kitL_placed kit) = loadVtablesAt kit := rfl

private theorem h45_segExit_mono_placed [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {x : WithStoresEncGhost} {R : SepProp} {s0 s : State} {p q : State → Prop}
    (h : SegExitPlaced kit st0 ikit ist0 C ctl parse S encRecord Hk x R s0 s p)
    (hpq : ∀ sf, p sf → q sf) :
    SegExitPlaced kit st0 ikit ist0 C ctl parse S encRecord Hk x R s0 s q := by
  intro hL
  obtain ⟨sf, hst, hp | hout⟩ := h hL
  · exact ⟨sf, hst, Or.inl (hpq sf hp)⟩
  · exact ⟨sf, hst, Or.inr hout⟩

private theorem h45_curStateV_of_false_placed [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {R : SepProp} {s0 s' : State}
    (h : ∃ r g sess, CurStateVPlaced (h45_kitF_placed kit) st0 ikit ist0 (fun _ => False) ctl encRecord x r g sess R s0 s') :
    ∃ r g sess, CurStateVPlaced kit st0 ikit ist0 Scope ctl encRecord x r g sess R s0 s' := by
  rcases h with ⟨r, _, _, _, ⟨hfalse, _⟩, _⟩
  exact False.elim hfalse

private theorem h45_curStateV_of_scopeNone_placed [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {R : SepProp} {s0 s' : State}
    (h : ∃ r g sess, CurStateVPlaced (h45_kitF_placed kit) st0 ikit ist0 (h45_ScopeNone_placed Scope) ctl encRecord x r g sess R s0 s') :
    ∃ r g sess, CurStateVPlaced kit st0 ikit ist0 Scope ctl encRecord x r g sess R s0 s' := by
  rcases h with ⟨r, g, sess, hcur, ⟨⟨hscope, _⟩, hl⟩, hrest⟩
  exact ⟨r, g, sess, hcur, ⟨hscope, hl⟩, hrest⟩

private theorem h45_loadOutRes_some_scopeNone_placed [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (A : RustAlloc) (w0 w1 w2 w3 w4 w5 w6 : BitVec 64) (tail : List (BitVec 8))
    {r : SessionRecord (List (BitVec 8))} (hcur : r.currentSession = none) :
    LoadOutResPlaced Scope A (.ok (some r)) w0 w1 w2 w3 w4 w5 w6 tail ⊢
      LoadOutResPlaced (h45_ScopeNone_placed Scope) A (.ok (some r)) w0 w1 w2 w3 w4 w5 w6 tail := by
  rw [loadOutResPlaced_some_eq, loadOutResPlaced_some_eq]
  apply Entails.sepExists_elim
  intro g
  refine Entails.trans ?_ (Entails.sepExists_intro g)
  refine Entails.pure_left fun ⟨hscope, hrest⟩ => ?_
  exact Entails.pure_right ⟨⟨hscope, hcur⟩, hrest⟩ (Entails.refl _)

set_option maxHeartbeats 800000 in
private theorem h45_segLoad_to_dispatch_placed [LibsignalPlacement] {F0 : SepProp}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hEnv : EncEnvTPlaced F0 kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord Hk)
    (x : WithStoresEncGhost) (R : SepProp) (s0 : State)
    (hfs : EncFsCtxPlaced kit ikit Hk s0 s0)
    (hpc0 : s0.pc = encEntryPlaced) (hrun0 : s0.status = .Running) (hal0 : s0.spAligned = true)
    (hm0 : s0.mem ⊨ (withStoresEncPlacedSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).pre x s0 ∗ R)
    (hcont : ∀ (s : State) (sp : BitVec 64)
      (ans : Except Unit (Option (SessionRecord (List (BitVec 8)))))
      (w0 w1 w2 w3 w4 w5 w6 v50 : BitVec 64) (tail : List (BitVec 8)),
      sp = s0.sp - 0xbe0#64 →
      s.pc = encEntryPlaced + 0x160#64 →
      encMidMetaPlaced x s0 s →
      x.ptext.length < 2 ^ 32 ∧ x.rest.length < 2 ^ 63 ∧ x.locA ≠ 0#64 ∧
        x.now.tvNsec.toNat < 10 ^ 9 ∧ withStoresEncStackV kit ikit ≤ s0.sp.toNat →
      w0 ≠ 0xFFFFFFFFFFFFFFFD#64 → tail.length = 312 →
      kit.loadRel st0 x.rem.val ans →
      s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans →
      s.readReg64 .x24 = w0 → s.readReg64 .x27 = w1 →
      s.readReg64 .x21 = w2 → s.readReg64 .x23 = w3 →
      s.readReg64 .x25 = sp + 0x580#64 →
      s.readReg64 .x26 = sp + 0x9d0#64 →
      s.readReg64 .x28 = sp + 0x4a0#64 →
      s.pstate = addsPState64 w0 2#64 →
      (s.mem ⊨ (memRegion (sp + 0x46a#64) 0x116 ∗
        memRegion (sp + 0x580#64) 368 ∗
        ((sp + 0x6f8#64) ↦ₛ tail) ∗
        ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗
        ((sp + 0x840#64) ↦₆₄ w6) ∗
        LoadOutResPlaced Scope A ans w0 w1 w2 w3 w4 w5 w6 tail ∗
        protocolAddressAt A x.rem x.remA ∗
        A.pool ∗ stackAt sp encSubStack ∗ loadVtablesAt kit ∗
        dispatchFramePlaced kit st0 ikit ist0 ctl x s0 v50) ∗ R) →
      SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s
        (fun s' => ∃ r g sess,
          CurStateVPlaced kit st0 ikit ist0 Scope ctl encRecord x r g sess R s0 s')) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s0
      (fun s' => ∃ r g sess,
        CurStateVPlaced kit st0 ikit ist0 Scope ctl encRecord x r g sess R s0 s') := by
  let envL := h45_envL_placed hEnv
  obtain ⟨hcrl0, hm0⟩ := StoreKit.extract_withLsCodeRoLoaded hm0
  dsimp only [withStoresEncPlacedSpecV] at hm0
  rw [cliTapeAt_eq_pure_sep_cliTapeAfter_zero] at hm0
  have hpull0 :
      (⌜s0.readReg64 .x0 = x.ptA ∧ (s0.readReg64 .x1).toNat = x.ptext.length ∧
          x.ptext.length < 2 ^ 32 ∧ s0.readReg64 .x2 = x.remA ∧ s0.readReg64 .x3 = x.locA ∧
          x.locA ≠ 0#64 ∧
          s0.readReg64 .x4 = x.ssA ∧ s0.readReg64 .x5 = kit.ss_vt ∧
          s0.readReg64 .x6 = x.idA ∧ s0.readReg64 .x7 = ikit.id_vt ∧
          x.now.tvNsec.toNat < 10 ^ 9 ∧ s0.readReg64 .x8 = x.ret ∧
          withStoresEncStackV kit ikit ≤ s0.sp.toNat ∧
          kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val⌝ ∗
        kit.storeAt x.ssA st0 ∗ ikit.identityAt x.idA ist0 ∗
        nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ memRegion x.ret 248 ∗
        (⌜x.rest.length < 2 ^ 63⌝ ∗ cliTapeAfter ctl x.cur x.rest 0) ∗
        FromRecordCallees.lsLogOff ∗ stackAt s0.sp (withStoresEncStackV kit ikit) ∗ A.pool) ∗ R =
      ⌜s0.readReg64 .x0 = x.ptA ∧ (s0.readReg64 .x1).toNat = x.ptext.length ∧
        x.ptext.length < 2 ^ 32 ∧ s0.readReg64 .x2 = x.remA ∧ s0.readReg64 .x3 = x.locA ∧
        x.locA ≠ 0#64 ∧
        s0.readReg64 .x4 = x.ssA ∧ s0.readReg64 .x5 = kit.ss_vt ∧
        s0.readReg64 .x6 = x.idA ∧ s0.readReg64 .x7 = ikit.id_vt ∧
        x.now.tvNsec.toNat < 10 ^ 9 ∧ s0.readReg64 .x8 = x.ret ∧
        withStoresEncStackV kit ikit ≤ s0.sp.toNat ∧
        kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val⌝ ∗
      (⌜x.rest.length < 2 ^ 63⌝ ∗
      ((nowAt s0.sp x.now ∗ stackAt s0.sp (withStoresEncStackV kit ikit) ∗
        (protocolAddressAt A x.rem x.remA ∗ kit.storeAt x.ssA st0 ∗ A.pool ∗
          ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.loc x.locA ∗ memRegion x.ret 248 ∗
            cliTapeAfter ctl x.cur x.rest 0 ∗ FromRecordCallees.lsLogOff ∗ ikit.identityAt x.idA ist0))) ∗ R)) := by
    sep_ac_rfl
  rw [hpull0] at hm0
  obtain ⟨⟨hx0, hx1_nat, hpt_lt, hx2, hx3, hloc_ne, hx4, hx5, hx6, hx7, hnsec, hx8, hsp_le, haddr_ss, _haddr_id⟩, hm0⟩ :=
    (satisfies_pure_sepConj _ _ _).mp hm0
  obtain ⟨hrest_lt, hm0⟩ := (satisfies_pure_sepConj _ _ _).mp hm0
  have hsub := encSubStackV_le_two_pow_64 kit ikit hsp_le
  have hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.ptext.length := by
    rw [← hx1_nat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hm_vt := loadVtablesPlaced_intro hEnv.vtables hcrl0.2 hm0
  have hpull_vt :
      loadVtablesAt kit ∗
        ((nowAt s0.sp x.now ∗ stackAt s0.sp (withStoresEncStackV kit ikit) ∗
          (protocolAddressAt A x.rem x.remA ∗ kit.storeAt x.ssA st0 ∗ A.pool ∗
            ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.loc x.locA ∗ memRegion x.ret 248 ∗
              cliTapeAfter ctl x.cur x.rest 0 ∗ FromRecordCallees.lsLogOff ∗ ikit.identityAt x.idA ist0))) ∗ R) =
      (nowAt s0.sp x.now ∗ stackAt s0.sp (withStoresEncStackV kit ikit) ∗ loadVtablesAt kit ∗
        (protocolAddressAt A x.rem x.remA ∗ kit.storeAt x.ssA st0 ∗ A.pool ∗
          ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.loc x.locA ∗ memRegion x.ret 248 ∗
            cliTapeAfter ctl x.cur x.rest 0 ∗ FromRecordCallees.lsLogOff ∗ ikit.identityAt x.idA ist0))) ∗ R := by
    sep_ac_rfl
  rw [hpull_vt] at hm_vt
  have hfsAt : FsAt kit.envOk (kit.Quiet ∧ ikit.Quiet) (lsProg_464 Hk) s0 :=
    (hfs.fsAt (evs := []) (List.append_nil _).symm (fun _ => NoFsEv.nil)).mono (fun _ h => h.1) id
  refine segExit_placed_of_sepWPp (target := encEntryPlaced + 0x160#64) hm_vt ?_
  have he0 := segLoad_shim_placed_wp envL x s0
    (protocolAddressAt A x.rem x.remA ∗ kit.storeAt x.ssA st0 ∗ A.pool ∗
      ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.loc x.locA ∗ memRegion x.ret 248 ∗
        cliTapeAfter ctl x.cur x.rest 0 ∗ FromRecordCallees.lsLogOff ∗ ikit.identityAt x.idA ist0))
    hsp_le rfl hpc0 hrun0 hal0 hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8
  refine messageEncrypt_of_sepWP_placed hcrl0 (SepWP.mono he0 ?_)
  intro sm P_m hpcm hrunm hpostm hcrlm
  rcases hpostm with ⟨v50, v470, v478, waker0, waker1, v830, v838, v840,
    hspm, halm, hfsm, htrm, hx0m, hx1m, hx19m, hx29m, hvregsm, hx30m, rfl⟩
  refine messageEncrypt_call_panic_then_sepWPp_placed
    (subroutine_ok_withStepsPost (hEnv.kitOk.loadShim (callerProg := lsProg_464 Hk) (callerBlk := 464) (by decide)))
    (x := ⟨x.ssA, x.remA⟩)
    (F := shimFramePlaced kit ikit ist0 ctl x s0 v50 ∗
      memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.loadShimStack) ∗
      memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 6 ∗
      ((s0.sp - 0xbe0#64 + 0x470#64) ↦₆₄ v470) ∗ ((s0.sp - 0xbe0#64 + 0x478#64) ↦₆₄ v478) ∗
      ((s0.sp - 0xbe0#64 + 0x480#64) ↦₆₄ waker0) ∗ ((s0.sp - 0xbe0#64 + 0x488#64) ↦₆₄ waker1) ∗
      ((s0.sp - 0xbe0#64 + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0xbe0#64 + 0x498#64) 0xe8 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x6f8#64) 312 ∗
      ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ v830) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ v838) ∗
      ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ v840) ∗
      protocolAddressAt A x.rem x.remA ∗
      kit.storeAt x.ssA st0 ∗
      loadVtablesAt kit)
    hcrlm hpcm hrunm halm hx30m ?_ ?_ (fun _ _ => rfl) ?_
  · intro R' hm'
    dsimp only [withStepsPost, ReachesOutcome.withStepsPost, withLsRoCl, kitLoadShimSpec, shimFramePlaced] at hm' ⊢
    rw [sepConj_comm _ ⌜LibsignalCodeRoLoaded lsmpl sm.mem⌝, sepConj_assoc]
    refine (satisfies_pure_sepConj _ _ _).mpr ⟨hcrlm, ?_⟩
    refine Satisfies.mono ?_ hm'
    have hpre_eq :
        (nowAt s0.sp x.now ∗
          encSavedRegs s0.sp s0 ∗
          stackAt sm.sp kit.loadShimStack ∗
          memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.loadShimStack) ∗
          memRegion (s0.sp - 0xbe0#64) 0x50 ∗
          ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ v50) ∗
          encSpillsInit kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
          ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x358 ∗
          ((s0.sp - 0xbe0#64 + 0x468#64) ↦₈ 0#8) ∗ ((s0.sp - 0xbe0#64 + 0x469#64) ↦₈ 0#8) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 6 ∗
          ((s0.sp - 0xbe0#64 + 0x470#64) ↦₆₄ v470) ∗ ((s0.sp - 0xbe0#64 + 0x478#64) ↦₆₄ v478) ∗
          ((s0.sp - 0xbe0#64 + 0x480#64) ↦₆₄ waker0) ∗ ((s0.sp - 0xbe0#64 + 0x488#64) ↦₆₄ waker1) ∗
          ((s0.sp - 0xbe0#64 + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0xbe0#64 + 0x498#64) 0xe8 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x6f8#64) 312 ∗
          ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ v830) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ v838) ∗
          ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ v840) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
          loadVtablesAt kit ∗
          (protocolAddressAt A x.rem x.remA ∗ kit.storeAt x.ssA st0 ∗ A.pool ∗
            ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.loc x.locA ∗ memRegion x.ret 248 ∗
              cliTapeAfter ctl x.cur x.rest 0 ∗ FromRecordCallees.lsLogOff ∗ ikit.identityAt x.idA ist0))) ∗ R' =
        (A.pool ∗ stackAt sm.sp kit.loadShimStack) ∗
        (((nowAt s0.sp x.now ∗
          encSavedRegs s0.sp s0 ∗
          memRegion (s0.sp - 0xbe0#64) 0x50 ∗
          ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ v50) ∗
          encSpillsInit kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
          ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x358 ∗
          ((s0.sp - 0xbe0#64 + 0x468#64) ↦₈ 0#8) ∗ ((s0.sp - 0xbe0#64 + 0x469#64) ↦₈ 0#8) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
          (x.ptA ↦ₛ x.ptext) ∗
          protocolAddressAt A x.loc x.locA ∗
          memRegion x.ret 248 ∗
          cliTapeAfter ctl x.cur x.rest 0 ∗
          FromRecordCallees.lsLogOff ∗
          ikit.identityAt x.idA ist0) ∗
          memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.loadShimStack) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 6 ∗
          ((s0.sp - 0xbe0#64 + 0x470#64) ↦₆₄ v470) ∗ ((s0.sp - 0xbe0#64 + 0x478#64) ↦₆₄ v478) ∗
          ((s0.sp - 0xbe0#64 + 0x480#64) ↦₆₄ waker0) ∗ ((s0.sp - 0xbe0#64 + 0x488#64) ↦₆₄ waker1) ∗
          ((s0.sp - 0xbe0#64 + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0xbe0#64 + 0x498#64) 0xe8 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x6f8#64) 312 ∗
          ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ v830) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ v838) ∗
          ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ v840) ∗
          protocolAddressAt A x.rem x.remA ∗
          kit.storeAt x.ssA st0 ∗
          loadVtablesAt kit) ∗ R') := by
      sep_ac_rfl
    rw [h45_encSubStackV_kitL, h45_loadVtablesAt_kitL, hpre_eq]
    apply sepConj_mono_left
    exact Entails.pure_right (And.intro hx0m hx1m) (Entails.refl _)
  · intro sf
    dsimp only [withStepsPost, ReachesOutcome.withStepsPost, withLsRoCl, kitLoadShimSpec]
    exact alloc_onPanic_placed_entails (by rw [htrm])
  · intro sf1 hpc1 hrun1 hsp1 hcs1 hcrl1
    rcases hcs1 with ⟨hcs19, _, _, _, _, _, _, _, _, _, hcs29, hcsv1⟩
    dsimp only [withStepsPost, ReachesOutcome.withStepsPost, withLsRoCl, kitLoadShimSpec]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hsteps1 => ?_
    refine SepWPp.pure_elim fun _hcrl1' => ?_
    refine SepWPp.pure_elim fun ⟨hx1_1, hbox_ne, _hbox_align, htr1⟩ => ?_
    have henv1 : kit.envOk sf1.fs.files :=
      (hfsAt.of_call hsteps1 (congrArg FsState.files hfsm) htr1).envOk_here
    set box := sf1.readReg64 .x0
    have hsp1' : sf1.sp = s0.sp - 0xbe0#64 := by rw [hsp1, hspm]
    have hal1 : sf1.spAligned = true := by rw [State.spAligned, hsp1, ← State.spAligned]; exact halm
    have hpre_poll := segLoad_pre_poll_placed_wp envL
      (s := sf1) (sp := s0.sp - 0xbe0#64) (box := box)
      (v470 := v470) (v478 := v478)
      (F := A.live box kit.loadBoxSize 8 ∗ kit.loadBoxAt box x.ssA x.remA 0#8 ∗
        A.pool ∗
        shimFramePlaced kit ikit ist0 ctl x s0 v50 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 6 ∗
        ((s0.sp - 0xbe0#64 + 0x480#64) ↦₆₄ waker0) ∗ ((s0.sp - 0xbe0#64 + 0x488#64) ↦₆₄ waker1) ∗
        ((s0.sp - 0xbe0#64 + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0xbe0#64 + 0x498#64) 0xe8 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x6f8#64) 312 ∗
        ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ v830) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ v838) ∗
        ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ v840) ∗
        protocolAddressAt A x.rem x.remA ∗
        kit.storeAt x.ssA st0)
      hsub hpc1 hrun1 hsp1' hal1 rfl hx1_1 hbox_ne
    have hpre_poll_eq :
        A.live box kit.loadBoxSize 8 ∗ kit.loadBoxAt box x.ssA x.remA 0#8 ∗
          A.pool ∗ stackAt sm.sp kit.loadShimStack ∗
          shimFramePlaced kit ikit ist0 ctl x s0 v50 ∗
          memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.loadShimStack) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 6 ∗
          ((s0.sp - 0xbe0#64 + 0x470#64) ↦₆₄ v470) ∗ ((s0.sp - 0xbe0#64 + 0x478#64) ↦₆₄ v478) ∗
          ((s0.sp - 0xbe0#64 + 0x480#64) ↦₆₄ waker0) ∗ ((s0.sp - 0xbe0#64 + 0x488#64) ↦₆₄ waker1) ∗
          ((s0.sp - 0xbe0#64 + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0xbe0#64 + 0x498#64) 0xe8 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x6f8#64) 312 ∗
          ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ v830) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ v838) ∗
          ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ v840) ∗
          protocolAddressAt A x.rem x.remA ∗
          kit.storeAt x.ssA st0 ∗
          loadVtablesAt kit =
        ((s0.sp - 0xbe0#64 + 0x470#64) ↦₆₄ v470) ∗ ((s0.sp - 0xbe0#64 + 0x478#64) ↦₆₄ v478) ∗
          stackAt sf1.sp kit.loadShimStack ∗
          memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.loadShimStack) ∗
          loadVtablesAt kit ∗
          (A.live box kit.loadBoxSize 8 ∗ kit.loadBoxAt box x.ssA x.remA 0#8 ∗
            A.pool ∗
            shimFramePlaced kit ikit ist0 ctl x s0 v50 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 6 ∗
            ((s0.sp - 0xbe0#64 + 0x480#64) ↦₆₄ waker0) ∗ ((s0.sp - 0xbe0#64 + 0x488#64) ↦₆₄ waker1) ∗
            ((s0.sp - 0xbe0#64 + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0xbe0#64 + 0x498#64) 0xe8 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x6f8#64) 312 ∗
            ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ v830) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ v838) ∗
            ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ v840) ∗
            protocolAddressAt A x.rem x.remA ∗
            kit.storeAt x.ssA st0) := by
      rw [hsp1]
      sep_ac_rfl
    rw [hpre_poll_eq]
    refine messageEncrypt_of_sepWP_placed hcrl1 (SepWP.mono hpre_poll ?_)
    intro sm2 P_m2 hpcm2 hrunm2 hpostm2 hcrlm2
    rcases hpostm2 with ⟨hspm2, halm2, hfsm2, htrm2, hx0m2, hx8m2, hx20m2, hx19m2, hx29m2, hvregsm2, hx30m2, rfl⟩
    refine messageEncrypt_call_panic_then_wp_placed
      (hEnv.kitOk.loadPoll (callerProg := lsProg_464 Hk) (callerBlk := 464) (by decide))
      (x := (⟨box, s0.sp - 0xbe0#64 + 0x580#64, x.remA, x.rem⟩, x.ssA, st0))
      (F := ((s0.sp - 0xbe0#64 + 0x470#64) ↦₆₄ box) ∗
        ((s0.sp - 0xbe0#64 + 0x478#64) ↦₆₄ (0#64 + kit.loadFutVtOff)) ∗
        memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.loadPollStack) ∗
        loadVtablesAt kit ∗
        A.live box kit.loadBoxSize 8 ∗
        shimFramePlaced kit ikit ist0 ctl x s0 v50 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 6 ∗
        ((s0.sp - 0xbe0#64 + 0x480#64) ↦₆₄ waker0) ∗ ((s0.sp - 0xbe0#64 + 0x488#64) ↦₆₄ waker1) ∗
        ((s0.sp - 0xbe0#64 + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0xbe0#64 + 0x498#64) 0xe8 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x6f8#64) 312 ∗
        ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ v830) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ v838) ∗
        ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ v840))
      hcrlm2 hpcm2 hrunm2 halm2 hx30m2 ?_ ?_ (fun _ _ => rfl) ?_
    · intro R' hm'
      dsimp only [withLsRoCl]
      rw [sepConj_comm _ ⌜LibsignalCodeRoLoaded lsmpl sm2.mem⌝, sepConj_assoc]
      refine (satisfies_pure_sepConj _ _ _).mpr ⟨hcrlm2, ?_⟩
      refine withEnvPre_pre_intro (hfsm2 ▸ henv1) ?_
      dsimp only [kitLoadPollPlacedSpecS] at hm' ⊢
      refine Satisfies.mono ?_ hm'
      rw [hspm2]
      have hperm_p :
          (((s0.sp - 0xbe0#64 + 0x470#64) ↦₆₄ box) ∗
            ((s0.sp - 0xbe0#64 + 0x478#64) ↦₆₄ (0#64 + kit.loadFutVtOff)) ∗
            memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.loadPollStack) ∗
            stackAt (s0.sp - 0xbe0#64) kit.loadPollStack ∗
            loadVtablesAt kit ∗
            (A.live box kit.loadBoxSize 8 ∗ kit.loadBoxAt box x.ssA x.remA 0#8 ∗
              A.pool ∗
              shimFramePlaced kit ikit ist0 ctl x s0 v50 ∗
              memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 6 ∗
              ((s0.sp - 0xbe0#64 + 0x480#64) ↦₆₄ waker0) ∗ ((s0.sp - 0xbe0#64 + 0x488#64) ↦₆₄ waker1) ∗
              ((s0.sp - 0xbe0#64 + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0xbe0#64 + 0x498#64) 0xe8 ∗
              memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
              memRegion (s0.sp - 0xbe0#64 + 0x6f8#64) 312 ∗
              ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ v830) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ v838) ∗
              ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ v840) ∗
              protocolAddressAt A x.rem x.remA ∗
              kit.storeAt x.ssA st0)) ∗ R' =
          (kit.loadBoxAt box x.ssA x.remA 0#8 ∗ kit.storeAt x.ssA st0 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
            protocolAddressAt A x.rem x.remA ∗ A.pool ∗
            stackAt (s0.sp - 0xbe0#64) kit.loadPollStack) ∗
          ((((s0.sp - 0xbe0#64 + 0x470#64) ↦₆₄ box) ∗
            ((s0.sp - 0xbe0#64 + 0x478#64) ↦₆₄ (0#64 + kit.loadFutVtOff)) ∗
            memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.loadPollStack) ∗
            loadVtablesAt kit ∗
            A.live box kit.loadBoxSize 8 ∗
            shimFramePlaced kit ikit ist0 ctl x s0 v50 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 6 ∗
            ((s0.sp - 0xbe0#64 + 0x480#64) ↦₆₄ waker0) ∗ ((s0.sp - 0xbe0#64 + 0x488#64) ↦₆₄ waker1) ∗
            ((s0.sp - 0xbe0#64 + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0xbe0#64 + 0x498#64) 0xe8 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x6f8#64) 312 ∗
            ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ v830) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ v838) ∗
            ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ v840)) ∗ R') := by
        sep_ac_rfl
      rw [h45_encSubStackV_kitL, h45_loadVtablesAt_kitL, hperm_p]
      apply sepConj_mono_left
      exact Entails.pure_right ⟨hx0m2, hx8m2, haddr_ss⟩ (Entails.refl _)
    · intro sf
      dsimp only [withLsRoCl, kitLoadPollPlacedSpecSE, kitLoadPollPlacedSpecS]
      exact alloc_onPanic_placed_entails (by rw [htrm2, htr1, htrm])
    · intro sf2 hpc2 hrun2 hsp2 hcs2
      rcases hcs2 with ⟨hcs2_19, hcs2_20, _, _, _, _, _, _, _, _, hcs2_29, hcs2_v⟩
      dsimp only [withLsRoCl, kitLoadPollPlacedSpecSE, kitLoadPollPlacedSpecS]
      wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWP.exists_elim; intro ans
      apply SepWP.pure_elim; rintro ⟨hcrl2, hl, htr2⟩
      have hsp2' : sf2.sp = s0.sp - 0xbe0#64 := by rw [hsp2, hspm2]
      have hal2 : sf2.spAligned = true := by rw [State.spAligned, hsp2, ← State.spAligned]; exact halm2
      have hx20_2 : sf2.readReg64 .x20 = s0.sp - 0xbe0#64 + 0x580#64 := by rw [hcs2_20, hx20m2]
      have he1 := segLoad_poll_placed_wp envL
        (s := sf2) (sp := s0.sp - 0xbe0#64) (box := box) (self := x.ssA) (remA := x.remA)
        (waker0 := waker0) (waker1 := waker1) (v830 := v830) (v838 := v838) (v840 := v840)
        (ans := ans)
        (F := protocolAddressAt A x.rem x.remA ∗ kit.storeAt x.ssA st0 ∗ shimFramePlaced kit ikit ist0 ctl x s0 v50)
        hsub hpc2 hrun2 hsp2' hal2 hx20_2 hcrl2
      refine sepWP_conseq_pc_run (by rw [hspm2, BitVec.zero_add]; sep_ac_rfl) he1 ?_
      intro sf P_f hpcf hrunf hpostf hcrlf hm_f
      rcases hpostf with ⟨w0, w1, w2, w3, w4, w5, w6, tail,
        hw0_ne, htail, hspf, half, htrf, hx19f, hx29f, hvregsf,
        hx24f, hx27f, hx21f, hx23f, hx25f, hx26f, hx28f, hpsf, rfl⟩
      have hm_f' : sf.mem ⊨ (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
          ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
          ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
          ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
          LoadOutResPlaced Scope A ans w0 w1 w2 w3 w4 w5 w6 tail ∗
          protocolAddressAt A x.rem x.remA ∗
          A.pool ∗ stackAt (s0.sp - 0xbe0#64) encSubStack ∗ loadVtablesAt kit ∗
          dispatchFramePlaced kit st0 ikit ist0 ctl x s0 v50) ∗ R := by
        refine Satisfies.mono ?_ hm_f
        refine sepConj_mono_left ?_
        have hsp_split := encSubStack_split_extra_placed kit st0 ikit ist0 x s0 hsp_le
        dsimp only [shimFramePlaced, dispatchFramePlaced]
        have hperm :
            memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
              memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
              ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
              ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
              ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
              LoadOutResPlaced Scope A ans w0 w1 w2 w3 w4 w5 w6 tail ∗
              A.pool ∗ stackAt (s0.sp - 0xbe0#64) (encSubStackV kit ikit) ∗ loadVtablesAt kit ∗
              (protocolAddressAt A x.rem x.remA ∗
                kit.storeAt x.ssA st0 ∗
                (nowAt s0.sp x.now ∗
                  encSavedRegs s0.sp s0 ∗
                  memRegion (s0.sp - 0xbe0#64) 0x50 ∗
                  ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ v50) ∗
                  encSpillsInit kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
                  ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
                  memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x358 ∗
                  ((s0.sp - 0xbe0#64 + 0x468#64) ↦₈ 0#8) ∗ ((s0.sp - 0xbe0#64 + 0x469#64) ↦₈ 0#8) ∗
                  memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
                  memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
                  (x.ptA ↦ₛ x.ptext) ∗
                  protocolAddressAt A x.loc x.locA ∗
                  memRegion x.ret 248 ∗
                  cliTapeAfter ctl x.cur x.rest 0 ∗
                  FromRecordCallees.lsLogOff ∗
                  ikit.identityAt x.idA ist0)) =
            (kit.storeAt x.ssA st0 ∗ ikit.identityAt x.idA ist0 ∗
              stackAt (s0.sp - 0xbe0#64) (encSubStackV kit ikit)) ∗
            (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
              memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
              ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
              ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
              ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
              LoadOutResPlaced Scope A ans w0 w1 w2 w3 w4 w5 w6 tail ∗
              protocolAddressAt A x.rem x.remA ∗
              A.pool ∗ loadVtablesAt kit ∗
              nowAt s0.sp x.now ∗
              encSavedRegs s0.sp s0 ∗
              memRegion (s0.sp - 0xbe0#64) 0x50 ∗
              ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ v50) ∗
              encSpillsInit kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
              ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
              memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x358 ∗
              ((s0.sp - 0xbe0#64 + 0x468#64) ↦₈ 0#8) ∗ ((s0.sp - 0xbe0#64 + 0x469#64) ↦₈ 0#8) ∗
              memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
              memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
              (x.ptA ↦ₛ x.ptext) ∗
              protocolAddressAt A x.loc x.locA ∗
              memRegion x.ret 248 ∗
              cliTapeAfter ctl x.cur x.rest 0 ∗
              FromRecordCallees.lsLogOff) := by
          sep_ac_rfl
        rw [h45_encSubStackV_kitL, h45_loadVtablesAt_kitL, hperm]
        refine Entails.trans (sepConj_mono_left hsp_split) ?_
        exact Entails.of_eq (by sep_ac_rfl)
      refine hcont sf (s0.sp - 0xbe0#64) ans w0 w1 w2 w3 w4 w5 w6 v50 tail rfl
        hpcf ⟨hrunf, hspf, hal0, half, ?_, ?_, hcrlf, ?_⟩
        ⟨hpt_lt, hrest_lt, hloc_ne, hnsec, hsp_le⟩
        hw0_ne htail hl ?_ hx24f hx27f hx21f hx23f hx25f hx26f hx28f hpsf hm_f'
      · rw [hx29f, hcs2_29, hx29m2, hcs29, hx29m]
      · rw [hx19f, hcs2_19, hx19m2, hcs19, hx19m]
      · rw [hvregsf, hcs2_v, hvregsm2, hcsv1, hvregsm]
      · rw [htrf, htr2, htrm2, htr1, htrm]

set_option maxHeartbeats 800000 in
theorem h45_segLoad_placed_okVT [LibsignalPlacement] {F0 : SepProp}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hEnv : EncEnvTPlaced F0 kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord Hk)
    (x : WithStoresEncGhost) (R : SepProp) (s0 : State)
    (hfs : EncFsCtxPlaced kit ikit Hk s0 s0)
    (hpc0 : s0.pc = encEntryPlaced) (hrun0 : s0.status = .Running) (hal0 : s0.spAligned = true)
    (hm0 : s0.mem ⊨ (withStoresEncPlacedSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).pre x s0 ∗ R) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s0
      (fun s' => ∃ r g sess,
        CurStateVPlaced kit st0 ikit ist0 Scope ctl encRecord x r g sess R s0 s') := by
  let envF := h45_envF_placed hEnv
  let envL := h45_envL_placed hEnv
  let envN := h45_envNone_placed hEnv
  refine h45_segLoad_to_dispatch_placed hEnv x R s0 hfs hpc0 hrun0 hal0 hm0 ?_
  intro s sp ans w0 w1 w2 w3 w4 w5 w6 v50 tail hsp_eq hpc hmeta hbnds _hw0_ne3 htail
    hl htr hx24 hx27 hx21 hx23 hx25 hx26 hx28 hps hm
  rcases ans with ⟨⟩ | (_ | r)
  · rw [← h45_segExit_kitF_placed]
    exact h45_segExit_mono_placed (segLoad_dispatch_err_placed envF x R s0 s sp w0 w1 w2 w3 w4 w5 w6 v50 tail
      hsp_eq hpc hmeta hbnds.2.2.2.2 htail hl htr hx27 hx21 hx23 hx25 hx26 hx28 hps hm)
      (fun _ => h45_curStateV_of_false_placed)
  · rw [← h45_segExit_kitF_placed]
    exact h45_segExit_mono_placed (segLoad_dispatch_none_placed envF x R s0 s sp w0 w1 w2 w3 w4 w5 w6 v50 tail
      hsp_eq hpc hmeta hbnds.2.2.2.2 htail hl htr hx24 hx26 hx28 hps hm)
      (fun _ => h45_curStateV_of_false_placed)
  · cases hcur : r.currentSession with
    | none =>
      have hmN : s.mem ⊨ (memRegion (sp + 0x46a#64) 0x116 ∗
          memRegion (sp + 0x580#64) 368 ∗
          ((sp + 0x6f8#64) ↦ₛ tail) ∗
          ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗
          ((sp + 0x840#64) ↦₆₄ w6) ∗
          LoadOutResPlaced (h45_ScopeNone_placed Scope) A (.ok (some r)) w0 w1 w2 w3 w4 w5 w6 tail ∗
          protocolAddressAt A x.rem x.remA ∗
          A.pool ∗ stackAt sp encSubStack ∗ loadVtablesAt kit ∗
          dispatchFramePlaced kit st0 ikit ist0 ctl x s0 v50) ∗ R := by
        refine Satisfies.mono ?_ hm
        exact sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left (h45_loadOutRes_some_scopeNone_placed A w0 w1 w2 w3 w4 w5 w6 tail hcur))))))))
      rw [← h45_segExit_kitF_placed]
      exact h45_segExit_mono_placed (segLoad_dispatch_some_placed envN x R s0 s r sp w0 w1 w2 w3 w4 w5 w6 v50 tail
        hsp_eq hpc hmeta hbnds htail hl htr hx24 hx27 hx21 hx23 hx25 hx26 hx28 hps hmN)
        (fun _ => h45_curStateV_of_scopeNone_placed)
    | some sess =>
      subst hsp_eq
      rcases hmeta with ⟨hrun, hsp, hal0, hal, hx29, hx19, hcrl, hvregs⟩
      rcases hbnds with ⟨hpt_lt, hrest_lt, hloc_ne, hnsec, hsp_le⟩
      have hm_drop : s.mem ⊨
          LoadOutResPlaced Scope A (.ok (some r)) w0 w1 w2 w3 w4 w5 w6 tail ∗
          ((memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
            ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
            ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
            ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
            protocolAddressAt A x.rem x.remA ∗
            A.pool ∗ stackAt (s0.sp - 0xbe0#64) encSubStack ∗
            dispatchFramePlaced kit st0 ikit ist0 ctl x s0 v50) ∗ R) := by
        refine Satisfies.drop_left (P := loadVtablesAt kit) ?_
        refine Satisfies.mono ?_ hm
        exact Entails.of_eq (by sep_ac_rfl)
      clear hm
      rw [loadOutResPlaced_some_eq] at hm_drop
      obtain ⟨g, hm_drop1⟩ := satisfies_sepExists_left hm_drop
      clear hm_drop
      rw [sepConj_assoc] at hm_drop1
      obtain ⟨⟨hscope, hcap_lt, hw0_eq, hw1_eq, hw2_eq, hw3_eq_init, htail_inl⟩, hm_drop2⟩ :=
        satisfies_pure_left hm_drop1
      clear hm_drop1
      subst hw0_eq hw1_eq hw2_eq hw3_eq_init
      obtain ⟨hw0_ne1, hw0_ne2, _⟩ := ne_neg_tags_of_lt_two_pow_63 hcap_lt
      have hm_cur : s.mem ⊨
          ⌜recordCurCap g ≠ 0xFFFFFFFFFFFFFFFF#64⌝ ∗
          ((((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ v50) ∗
            ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
            memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x358 ∗
            ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
            ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
            ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
            (recordHeap A g r ∗
              memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
              memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
              protocolAddressAt A x.rem x.remA ∗
              A.pool ∗ stackAt (s0.sp - 0xbe0#64) encSubStack ∗
              memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
              dispatchFrameNoRecPlaced kit st0 ikit ist0 ctl x s0)) ∗ R) := by
        refine Satisfies.mono ?_ hm_drop2
        refine Entails.trans (sepConj_mono_left (curSession_some_of_recordTailInline htail_inl hcur)) ?_
        rw [dispatchFramePlaced_eq_rec_sep kit st0 ikit ist0 ctl x s0 v50]
        exact Entails.of_eq (by sep_ac_rfl)
      clear hm_drop2
      obtain ⟨hw3_ne, hm_cur'⟩ := satisfies_pure_left hm_cur
      clear hm_cur
      refine segExit_placed_of_sepWP_frozen hcrl hm_cur'
        (segLoad_dispatch_some_cur_placed_wp envL hpc hrun hsp hal hw0_ne1 hw0_ne2 hw3_ne htail
          hx24 hx27 hx21 hx23 hx25 hx26 hx28 hps) ?_
      intro sf P_f hpcf hrunf hpostf hcrlf hm_f
      rcases hpostf with ⟨hspf, half, htrf, hx19f, hx29f, hvregsf, hx20f, hx21f, hx25f, hx26f, hx28f, rfl⟩
      refine segExit_placed_done ⟨r, g, sess, hcur, ⟨hscope, hl⟩, ?_⟩
      refine ⟨hpcf, ⟨hrunf, hspf, hal0, half, by rw [hx29f, hx29], by rw [hx19f, hx19], hcrlf, by rw [hvregsf, hvregs]⟩,
        by rw [htrf, htr],
        ⟨hx20f, hx21f, hx25f, hx26f, hx28f⟩,
        hpt_lt, hrest_lt, hloc_ne, hnsec, enc_sp_bound_of_kit kit ikit hsp_le, ?_⟩
      dsimp only [EncSeamVPlaced, curScratch]
      refine Satisfies.mono ?_ hm_f
      have hrec := sessionRecordAt_of_words56_sep_tail A (s0.sp - 0xbe0#64 + 0x110#64) g r htail_inl
      have h38 : (s0.sp - 0xbe0#64 + 0x110#64) + 0x38#64 = s0.sp - 0xbe0#64 + 0x148#64 := by bv_arith
      rw [h38] at hrec
      have h46a := memRegion_0x46a_0x716_fold (s0.sp - 0xbe0#64) w4 w5 w6 tail htail
      have hspills := encSpillsAt_fold kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x
      have hperm_cur :
          (recordWords56At (s0.sp - 0xbe0#64 + 0x110#64) g.prevCap g.prevPtr 0#64 (recordCurCap g) w4 w5 w6 ∗
            ((s0.sp - 0xbe0#64 + 0x148#64) ↦ₛ tail) ∗
            memRegion (s0.sp - 0xbe0#64 + 0x280#64) 0x1e8 ∗
            ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ (s0.sp - 0xbe0#64 + 0x128#64)) ∗
            ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
            ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
            ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
            ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
            (recordHeap A g r ∗
              memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
              memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
              protocolAddressAt A x.rem x.remA ∗
              A.pool ∗ stackAt (s0.sp - 0xbe0#64) encSubStack ∗
              memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
              dispatchFrameNoRecPlaced kit st0 ikit ist0 ctl x s0)) ∗ R =
          (recordWords56At (s0.sp - 0xbe0#64 + 0x110#64) g.prevCap g.prevPtr 0#64 (recordCurCap g) w4 w5 w6 ∗
            ((s0.sp - 0xbe0#64 + 0x148#64) ↦ₛ tail) ∗ recordHeap A g r) ∗
          (encSpillsInit kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗ ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA)) ∗
          (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
            ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
            ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
            ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
            memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338) ∗
          (memRegion (s0.sp - 0xbe0#64 + 0x280#64) 0x1e8 ∗
            ((s0.sp - 0xbe0#64 + 0x468#64) ↦₈ 0#8) ∗ ((s0.sp - 0xbe0#64 + 0x469#64) ↦₈ 0#8) ∗
            memRegion (s0.sp - 0xbe0#64) 0x50 ∗
            ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ (s0.sp - 0xbe0#64 + 0x128#64)) ∗
            memRegion x.ret 248 ∗
            encCommonPlaced A ctl x 0 s0 ∗ (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R)) := by
        dsimp only [dispatchFrameNoRecPlaced, encCommonPlaced]
        sep_ac_rfl
      rw [hperm_cur]
      refine Entails.trans (sepConj_mono hrec (sepConj_mono hspills (sepConj_mono_left h46a))) ?_
      exact Entails.of_eq (by sep_ac_rfl)

end SegLoad

section SegSignal
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom

private def h45_segSignalEncCallFramePlaced {ss_vt id_vt : BitVec 64} (A : RustAlloc)
    (x : WithStoresEncGhost)
    (g : RecordGhost) (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (k : IdentityKey) (sp : BitVec 64) (s0 : State) : SepProp :=
  sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
  ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
  ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8 ∗
  cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
  memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5f8#64) 0x588 ∗
  memRegion x.ret 248 ∗
  protocolAddressAt A x.loc x.locA ∗ nowAt s0.sp x.now ∗
  memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - rootStack) ∗
  encSavedRegs s0.sp s0

set_option maxHeartbeats 800000 in
private theorem h45_segSignal_enc_pre_unpack [LibsignalPlacement] {ss_vt id_vt : BitVec 64}
    (F0 : SepProp) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (k : IdentityKey) (sp : BitVec 64) (R : SepProp) (s0 s : State)
    (hsp0 : s0.sp - 0xbe0#64 = sp) (hsp : s.sp = sp)
    (hQ : otr.pqrState.length < 2 ^ 32) (h64 : 64 ≤ x.rest.length)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = sp + 0x580#64) (hx1 : s.readReg64 .x1 = sp + 0x288#64)
    (hx2 : s.readReg64 .x2 = x.ptA) (hx3 : s.readReg64 .x3 = BitVec.ofNat 64 x.ptext.length)
    (hx4 : s.readReg64 .x4 = 0#64) (hx5 : s.readReg64 .x5 = x.remA)
    (hpt : x.ptext.length < 2 ^ 32) (hrest : x.rest.length < 2 ^ 63)
    (hm : s.mem ⊨
      (takenSlots A sp sess taken ∗ otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
      cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      (memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 120 ∗
        memRegion (sp + 0x5f8#64) 0x588) ∗
      memRegion x.ret 248 ∗ encCommonPlaced A ctl x 0 s0 ∗ (F0 ∗ R)) :
    ∃ g : RecordGhost,
      s.mem ⊨ (StoreKit.withLsRoCl lsmpl (otrEncryptPlacedSpecQT F0 C A ctl uuidTryParse S)).pre
          (segSignalEncGhost sp pqCap pqPtr otr x) s ∗
        (h45_segSignalEncCallFramePlaced (ss_vt := ss_vt) (id_vt := id_vt) A x g sess taken k sp s0 ∗ R) := by
  unfold takenSlots encCommonPlaced at hm
  rw [hsp0, stackAt_sub sp encSubStack rootStack] at hm
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨g, hm⟩ := hm
  refine ⟨g, ?_⟩
  have htape := cliTapeAfter_zero_entails_cliTapeAt ctl x.cur x.rest hrest
  have hm_rearr : s.mem ⊨
      cliTapeAfter ctl x.cur x.rest 0 ∗
      (F0 ∗ otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
        (x.ptA ↦ₛ x.ptext) ∗
        protocolAddressAt A x.rem x.remA ∗
        memRegion (sp + 0x580#64) 120 ∗
        FromRecordCallees.lsLogOff ∗
        stackAt sp rootStack ∗
        A.pool ∗
        h45_segSignalEncCallFramePlaced (ss_vt := ss_vt) (id_vt := id_vt) A x g sess taken k sp s0 ∗ R) := by
    unfold h45_segSignalEncCallFramePlaced
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by sep_ac_rfl)) hm
  have hm_tape := Satisfies.mono (sepConj_mono_left htape) hm_rearr
  have hx3_nat : (s.readReg64 .x3).toNat = x.ptext.length := by
    rw [hx3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold StoreKit.withLsRoCl otrEncryptPlacedSpecQT otrEncryptPlacedSpecQF otrEncryptPlacedSpec segSignalEncGhost optAddrAt
  dsimp only
  rw [hsp, emp_sepConj]
  have hpure :
      (⌜StoreKit.LibsignalCodeRoLoaded lsmpl s.mem⌝ : SepProp) ∗
      ⌜otr.pqrState.length < 2 ^ 32 ∧ 64 ≤ x.rest.length⌝ ∗
      ⌜s.readReg64 .x0 = sp + 0x580#64 ∧ s.readReg64 .x1 = sp + 0x288#64 ∧
        s.readReg64 .x2 = x.ptA ∧ (s.readReg64 .x3).toNat = x.ptext.length ∧
        x.ptext.length < 2 ^ 32 ∧
        s.readReg64 .x4 = (if (none : Option AddrGhost).isSome then 0#64 else 0#64) ∧
        ((none : Option AddrGhost).isSome → 0#64 ≠ 0#64) ∧
        s.readReg64 .x5 = x.remA⌝ ∗
      (cliTapeAt ctl x.cur x.rest ∗
        (F0 ∗ otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
          (x.ptA ↦ₛ x.ptext) ∗
          protocolAddressAt A x.rem x.remA ∗
          memRegion (sp + 0x580#64) 120 ∗
          FromRecordCallees.lsLogOff ∗
          stackAt sp rootStack ∗
          A.pool ∗
          h45_segSignalEncCallFramePlaced (ss_vt := ss_vt) (id_vt := id_vt) A x g sess taken k sp s0 ∗ R)) =
      (((⌜otr.pqrState.length < 2 ^ 32 ∧ 64 ≤ x.rest.length⌝ ∗
          F0 ∗
          (⌜s.readReg64 .x0 = sp + 0x580#64 ∧ s.readReg64 .x1 = sp + 0x288#64 ∧
            s.readReg64 .x2 = x.ptA ∧ (s.readReg64 .x3).toNat = x.ptext.length ∧
            x.ptext.length < 2 ^ 32 ∧
            s.readReg64 .x4 = (if (none : Option AddrGhost).isSome then 0#64 else 0#64) ∧
            ((none : Option AddrGhost).isSome → 0#64 ≠ 0#64) ∧
            s.readReg64 .x5 = x.remA⌝ ∗
          otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
          (x.ptA ↦ₛ x.ptext) ∗
          protocolAddressAt A x.rem x.remA ∗
          memRegion (sp + 0x580#64) 120 ∗
          cliTapeAt ctl x.cur x.rest ∗
          FromRecordCallees.lsLogOff ∗
          stackAt sp rootStack ∗
          A.pool)) ∗
        ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s.mem⌝) ∗
        (h45_segSignalEncCallFramePlaced (ss_vt := ss_vt) (id_vt := id_vt) A x g sess taken k sp s0 ∗ R)) := by
    sep_ac_rfl
  rw [← hpure, satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj]
  exact ⟨hcrl, ⟨hQ, h64⟩, ⟨hx0, hx1, hx2, hx3_nat, hpt, hx4, (by intro h; cases h), hx5⟩, hm_tape⟩

set_option maxHeartbeats 800000 in
private theorem h45_segSignal_enc_post_pack [LibsignalPlacement] {ss_vt id_vt : BitVec 64}
    (F0 : SepProp) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (x : WithStoresEncGhost) (g : RecordGhost)
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (sp : BitVec 64) (R : SepProp) (s0 s sm : State)
    (hsp0 : s0.sp - 0xbe0#64 = sp) (hsp : s.sp = sp)
    (hpost : sm.mem ⊨
      ((StoreKit.withLsRoCl lsmpl (otrEncryptPlacedSpecQT F0 C A ctl uuidTryParse S)).post
          (segSignalEncGhost sp pqCap pqPtr otr x) s sm ∗
        h45_segSignalEncCallFramePlaced (ss_vt := ss_vt) (id_vt := id_vt) A x g sess taken k sp s0) ∗ R) :
    StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem ∧
    (segSignalRes C S x otr).1 ≠ .error .panic ∧ sm.trace = s.trace ∧
    (sm.mem ⊨
      (sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
        ((sp + 0x469#64) ↦₈ 1#8) ∗
        (∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64,
          otrAt A (sp + 0x288#64) pqCap' pqPtr' (segSignalRes C S x otr).2) ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
      cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      (memRegion (sp + 0x46a#64) 0x116 ∗
        signalMessageResultAt A (utf8 "encrypt") (sp + 0x580#64) (segSignalRes C S x otr).1 ∗
        memRegion (sp + 0x5f8#64) 0x588) ∗
      memRegion x.ret 248 ∗ encCommonPlaced A ctl x (S.draws otr.pqrState x.rest) s0 ∗ (F0 ∗ R)) := by
  unfold StoreKit.withLsRoCl otrEncryptPlacedSpecQT otrEncryptPlacedSpecQF otrEncryptPlacedSpec at hpost
  dsimp only at hpost
  rw [segSignalEncGhost_model, hsp] at hpost
  unfold segSignalEncGhost optAddrAt at hpost
  dsimp only at hpost
  rw [emp_sepConj] at hpost
  have h1 : sm.mem ⊨ ⌜StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem⌝ ∗
      ⌜(segSignalRes C S x otr).1 ≠ .error .panic ∧ sm.trace = s.trace⌝ ∗
      ((F0 ∗ (∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64,
          otrAt A (sp + 0x288#64) pqCap' pqPtr' (segSignalRes C S x otr).2) ∗
        signalMessageResultAt A (utf8 "encrypt") (sp + 0x580#64) (segSignalRes C S x otr).1 ∗
        (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗
        cliTapeAfter ctl x.cur x.rest (S.draws otr.pqrState x.rest) ∗
        FromRecordCallees.lsLogOff ∗ stackAt sp rootStack ∗ A.pool ∗
        h45_segSignalEncCallFramePlaced (ss_vt := ss_vt) (id_vt := id_vt) A x g sess taken k sp s0) ∗ R) :=
    Eq.mp (congrArg (sm.mem ⊨ ·) (by sep_ac_rfl)) hpost
  rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at h1
  rcases h1 with ⟨hcrlm, ⟨hne, htr⟩, hmem⟩
  refine ⟨hcrlm, hne, htr, ?_⟩
  unfold h45_segSignalEncCallFramePlaced at hmem
  have hmem_rearr : sm.mem ⊨
      (memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - rootStack) ∗
        stackAt sp rootStack) ∗
      (sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
        ((sp + 0x469#64) ↦₈ 1#8) ∗
        (∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64,
          otrAt A (sp + 0x288#64) pqCap' pqPtr' (segSignalRes C S x otr).2) ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8 ∗
        cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
        memRegion (sp + 0x46a#64) 0x116 ∗
        signalMessageResultAt A (utf8 "encrypt") (sp + 0x580#64) (segSignalRes C S x otr).1 ∗
        memRegion (sp + 0x5f8#64) 0x588 ∗
        memRegion x.ret 248 ∗
        (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest (S.draws otr.pqrState x.rest) ∗
        FromRecordCallees.lsLogOff ∗ encSavedRegs s0.sp s0 ∗ A.pool ∗ (F0 ∗ R)) :=
    Eq.mp (congrArg (sm.mem ⊨ ·) (by sep_ac_rfl)) hmem
  rw [← stackAt_sub sp encSubStack rootStack] at hmem_rearr
  unfold encCommonPlaced
  rw [hsp0]
  exact Eq.mp (congrArg (sm.mem ⊨ ·) (by sep_ac_rfl)) hmem_rearr

theorem h45_q_otr_placed [LibsignalPlacement] {F0 : SepProp} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hEnv : EncEnvTPlaced F0 kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord Hk)
    {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} (hcur : r.currentSession = some sess)
    (hsc : kit.ScopeAt Scope st0 x.rem.val r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken)) :
    otr.pqrState.length < 2 ^ 32 :=
  fromSessionState_pqrState hfrom ▸ hEnv.scopeQ r sess hsc hcur

theorem h45_segSignal_enc_to_ret_pf_placed [LibsignalPlacement]
    {F0 : SepProp} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hEnv : EncEnvTPlaced F0 kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord Hk)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (R_frame : SepProp) (s0 s : State)
    (h64 : 64 ≤ x.rest.length)
    (hs : SegSignalEncStateVPlaced kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k
      (F0 ∗ R_frame) s0 s) :
    h45_SegExitVTPlaced F0 kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R_frame s0 s
      (fun s' => SegSignalRetStateVPlaced kit st0 ikit ist0 Scope C ctl S encRecord x r sess otr taken k
        (F0 ∗ R_frame) s0 s') := by
  let R := encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R_frame
  rcases hs with ⟨hcur, hsc, hfrom, hrem, hnone, hs_pc, hs_lr,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hcrl, hvregs⟩,
    htr, hx0, hx1, hx2, hx3, hx4, hx5, hx20, hx25, hx26, hx28,
    hpt, hrest, hloc, hnow, hstk, hm⟩
  set sp := s0.sp - 0xbe0#64 with hsp0
  have hQ : otr.pqrState.length < 2 ^ 32 := h45_q_otr_placed hEnv hcur hsc hfrom
  have hm' : s.mem ⊨
      (takenSlots A sp sess taken ∗ otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
      cmScratch sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
      (memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 120 ∗
        memRegion (sp + 0x5f8#64) 0x588) ∗
      memRegion x.ret 248 ∗ encCommonPlaced A ctl x 0 s0 ∗ (F0 ∗ R) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by dsimp only [R]; sep_ac_rfl)) hm
  obtain ⟨g, hm_pre⟩ := h45_segSignal_enc_pre_unpack F0 C A ctl S x sess otr taken pqCap pqPtr k sp R
    s0 s hsp0.symm hsp hQ h64 hcrl hx0 hx1 hx2 hx3 hx4 hx5 hpt hrest hm'
  refine h45_segExitVT_call_sub_placed hEnv.callees.otrEnc (segSignalEncGhost sp pqCap pqPtr otr x)
    hs_pc hrun hal hs_lr hm_pre
    (fun _ code _ _ hex => by
      rw [show (StoreKit.withLsRoCl lsmpl (otrEncryptPlacedSpecQT F0 C A ctl uuidTryParse S)).onExit
            (segSignalEncGhost sp pqCap pqPtr otr x) code s _ = ⌜False⌝ from rfl,
          satisfies_pure_sepConj] at hex
      exact hex.1)
    (fun sf _ _ hpost =>
      segSignal_panic_bridge_placed (Q := fun _ => True) hcur hsc hnone hfrom hrem htr hpost)
    ?_
  intro sm _hL1 _hsteps12 hsm_pc hsm_run hsm_sp hcsm hpost
  have hsm_sp' : sm.sp = sp := hsm_sp.trans hsp
  have hsm_al : sm.spAligned = true := Pf.SegFrom.spAligned_of_sp_eq hal hsm_sp
  obtain ⟨hcrlm, hne, hsm_tr, hm_ret⟩ :=
    h45_segSignal_enc_post_pack F0 C A ctl S x g sess otr taken pqCap pqPtr k sp R s0 s sm
      hsp0.symm hsp hpost
  have hm_ret' : sm.mem ⊨
      (sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
        ((sp + 0x469#64) ↦₈ 1#8) ∗
        (∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64,
          otrAt A (sp + 0x288#64) pqCap' pqPtr' (segSignalRes C S x otr).2) ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
      cmScratch sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
      (memRegion (sp + 0x46a#64) 0x116 ∗
        signalMessageResultAt A (utf8 "encrypt") (sp + 0x580#64) (segSignalRes C S x otr).1 ∗
        memRegion (sp + 0x5f8#64) 0x588) ∗
      memRegion x.ret 248 ∗ encCommonPlaced A ctl x (S.draws otr.pqrState x.rest) s0 ∗
      (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ (F0 ∗ R_frame)) :=
    Eq.mp (congrArg (sm.mem ⊨ ·) (by dsimp only [R]; sep_ac_rfl)) hm_ret
  exact h45_segExitVT_of_segExit_placed (SegExitPlaced.next ⟨hcur, hsc, hfrom, hrem, hnone, hne, hsm_pc,
    ⟨hsm_run, hsm_sp', hal0, hsm_al,
      (hcsm.2.2.2.2.2.2.2.2.2.2.1).trans hx29,
      (hcsm.1).trans hx19,
      hcrlm,
      (hcsm.2.2.2.2.2.2.2.2.2.2.2).trans hvregs⟩,
    hsm_tr.trans htr,
    (hcsm.2.1).trans hx20,
    (hcsm.2.2.2.2.2.2.1).trans hx25,
    (hcsm.2.2.2.2.2.2.2.1).trans hx26,
    (hcsm.2.2.2.2.2.2.2.2.2.1).trans hx28,
    hpt, hrest, hloc, hnow, hstk, g, hm_ret'⟩)

end SegSignal

end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt

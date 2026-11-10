/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg2Placed
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegApplyStorePlaced
public import ProofLib.RegChain
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs

@[expose] public section

set_option autoImplicit false

/-!
# Relocatable CLI `MessageEncrypt` `WithStoresVT` (Part 3): `SegApplyStore`
-/

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt

open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.CliRatchet.EncPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

section SegApplyStore
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom
  (SegExitPlaced.next SegExitPlaced.of_false SegExitPlaced.of_sepWP)
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

private theorem cs_x19 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x19 = s0.readReg64 .x19 := h.1
private theorem cs_x20 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x20 = s0.readReg64 .x20 := h.2.1
private theorem cs_x21 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x21 = s0.readReg64 .x21 := h.2.2.1
private theorem cs_x22 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x22 = s0.readReg64 .x22 := h.2.2.2.1
private theorem cs_x23 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x23 = s0.readReg64 .x23 := h.2.2.2.2.1
private theorem cs_x25 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x25 = s0.readReg64 .x25 := h.2.2.2.2.2.2.1
private theorem cs_x26 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x26 = s0.readReg64 .x26 := h.2.2.2.2.2.2.2.1
private theorem cs_x27 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x27 = s0.readReg64 .x27 := h.2.2.2.2.2.2.2.2.1
private theorem cs_x28 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x28 = s0.readReg64 .x28 := h.2.2.2.2.2.2.2.2.2.1
private theorem cs_x29 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x29 = s0.readReg64 .x29 := h.2.2.2.2.2.2.2.2.2.2.1
private theorem cs_vregs {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : calleeSavedVRegs sf = calleeSavedVRegs s0 := h.2.2.2.2.2.2.2.2.2.2.2

private theorem storeShimStack_le_encSubStackV_placed {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) :
    kit.storeShimStack ≤ encSubStackV kit ikit := by
  unfold encSubStackV; omega

private theorem storePollStack_le_encSubStackV_placed {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) :
    kit.storePollStack ≤ encSubStackV kit ikit := by
  unfold encSubStackV; omega

private theorem allocHookStack_le_encSubStackV_placed {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) :
    allocHookStack ≤ encSubStackV kit ikit := by
  unfold encSubStackV encSubStack withStoresEncStack encFrameSize entryStack allocHookStack
  omega

private theorem entails_anyHeap_self_placed (R : SepProp) : R ⊢ anyHeap ∗ R :=
  Entails.trans (Entails.of_eq (emp_sepConj R).symm) (sepConj_mono_left (entails_anyHeap emp))

theorem h45_store_to_e80_placed [LibsignalPlacement] {F0 : SepProp} {Scope C A}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl S encRecord Hk}
    (hEnv : EncEnvTPlaced F0 kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord Hk)
    {x : WithStoresEncGhost} {g' : RecordGhost}
    {rec' : SessionRecord (List (BitVec 8))} {F R : SepProp} {s0 s : State}
    {next : State → Prop}
    (hrecOk : kit.RecOk rec')
    (haddr : kit.addrOk x.rem.val)
    (hbound : withStoresEncStackV kit ikit ≤ s0.sp.toNat)
    (hpc : s.pc = encEntryPlaced + 0xde8#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = s.sp + 0x58#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x580#64)
    (hpref0 : s0.trace <+: s.trace)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hfs : FsCtx kit.envOk True (lsProg_464 Hk) s s)
    (hm : s.mem ⊨ (storeVtablesAt kit ∗
      storeBaseActive kit st0 ikit s.sp x g' rec' ∗
      memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
      memRegion (s.sp + 0x9b0#64) 24) ∗ (F ∗ R))
    (hcont : ∀ sm (ans : Except Unit Unit) (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp),
      Steps (lsProg_464 Hk) s sm →
      sm.pc = encEntryPlaced + 0xe80#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.spAligned = true →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s.trace ++ kit.storeEvs encRecord x.rem.val rec' ans →
      kit.storeRel st0 x.rem.val rec' ans →
      (ans = .ok () → H = emp) →
      (ans = .error () →
        H = (w1 ↦ᵣ storeHookStr) ∧ w2 = 10#64 ∧ w3 = 1#64) →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x25 = s.readReg64 .x25 →
      sm.readReg64 .x26 = s.readReg64 .x26 →
      sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sm = calleeSavedVRegs s →
      sm.readReg64 .x27 = w0 →
      sm.readReg64 .x21 = w1 →
      sm.readReg64 .x23 = w2 →
      w0 = pollTag ans →
      (sm.mem ⊨ (storeBaseActive kit (kit.storeUpdate st0 x.rem.val rec' ans) ikit s.sp x g' rec' ∗
        memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
        (((s.sp + 0x9b0#64) ↦₆₄ w3) ∗ ((s.sp + 0x9b8#64) ↦₆₄ w4) ∗ ((s.sp + 0x9c0#64) ↦₆₄ w5)) ∗
        H) ∗ (F ∗ R)) →
      SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 sm next) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s next := by
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
  have hm1 : s.mem ⊨ (((s.sp + 0xc0#64) ↦₆₄ x.remA) ∗ ((s.sp + 0xd0#64) ↦₆₄ x.ssA) ∗
      ((s.sp + 0xd8#64) ↦₆₄ kit.ss_vt) ∗ ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (0#64 + kit.storeShimOff))) ∗
      (((((0#64 + kit.storeFutVtOff) ↦₆₄ᵣ (0#64 + kit.storeFutDropOff)) ∗
        ((0#64 + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
        ((0#64 + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.storePollOff)) ∗
        sessionRecordAt A (s.sp + 0x110#64) g' rec' ∗ protocolAddressAt A x.rem x.remA ∗
        stackAt s.sp (encSubStackV kit ikit) ∗ A.pool ∗ kit.storeAt x.ssA st0 ∗
        memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
        memRegion (s.sp + 0x9b0#64) 24) ∗ F) ∗ R) := by
    dsimp only [storeVtablesAt, storeBaseActive] at hm
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm
  refine SegExitPlaced.of_sepWP hm1 (step_de8_to_df8_placed hpc hrun hsp_align hx20) ?_
  rintro s1 P1 _ hsteps1 hpc1 hrun1 hm2
    ⟨rfl, hsp1, htr1, hx0_1, hx1_1, hx2_1, hx30_1, hx19_1, hx20_1, hx25_1, hx26_1, hx28_1, hx29_1, hvregs_1⟩
  have hsp1_al : s1.spAligned = true :=
    CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hsp_al hsp1
  have hpref1 : s0.trace <+: s1.trace := by rw [htr1]; exact hpref0
  have hcrl1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem := hcrl.of_keepsFrozen hsteps1.keepsFrozen
  have hm3 : s1.mem ⊨ (kitStoreShimSpec kit).pre ⟨x.ssA, x.remA, s.sp + 0x110#64⟩ s1 ∗
      ((((s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xd0#64) ↦₆₄ x.ssA ∗ (s.sp + 0xd8#64) ↦₆₄ kit.ss_vt ∗
        ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (0#64 + kit.storeShimOff)) ∗
        ((0#64 + kit.storeFutVtOff) ↦₆₄ᵣ (0#64 + kit.storeFutDropOff)) ∗
        ((0#64 + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
        ((0#64 + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.storePollOff)) ∗
        sessionRecordAt A (s.sp + 0x110#64) g' rec' ∗ protocolAddressAt A x.rem x.remA ∗
        kit.storeAt x.ssA st0 ∗
        memRegion (s.sp - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.storeShimStack) ∗
        memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
        memRegion (s.sp + 0x9b0#64) 24) ∗ F) ∗ R) := by
    dsimp only [kitStoreShimSpec]
    rw [hsp1]
    rw [stackAt_encSubStackV_split kit ikit hbound s.sp kit.storeShimStack
      (storeShimStack_le_encSubStackV_placed kit ikit)] at hm2
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_1, hx1_1, hx2_1⟩, Eq.mp (congrArg (s1.mem ⊨ ·) (by ac_rfl)) hm2⟩
  refine call_rocl_alloc_placed (hEnv.kitOk.storeShim (by decide)) ⟨x.ssA, x.remA, s.sp + 0x110#64⟩
    hpc1 hrun1 hsp1_al hx30_1 hpref1 hcrl1 hm3 ?_ (hR := entails_anyHeap_self_placed R)
  intro s2 hsteps2 hpc2 hrun2 hsp2 hsp2_al hcs2 hcrl2 hm4
  dsimp only [kitStoreShimSpec] at hm4
  rw [hsp1] at hsp2 hm4
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm4
  obtain ⟨⟨hx1_2, htr2⟩, hm4⟩ := hm4
  set box := s2.readReg64 .x0
  have hm4' : s2.mem ⊨ memRegion (s.sp + 0x470#64) 16 ∗
      ((A.live box kit.storeBoxSize 8 ∗ kit.storeBoxAt box x.ssA x.remA (s.sp + 0x110#64) 0#8 ∗ A.pool ∗
        kit.storeAt x.ssA st0 ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xd0#64) ↦₆₄ x.ssA ∗ (s.sp + 0xd8#64) ↦₆₄ kit.ss_vt ∗
        ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (0#64 + kit.storeShimOff)) ∗
        ((0#64 + kit.storeFutVtOff) ↦₆₄ᵣ (0#64 + kit.storeFutDropOff)) ∗
        ((0#64 + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
        ((0#64 + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.storePollOff)) ∗
        sessionRecordAt A (s.sp + 0x110#64) g' rec' ∗ protocolAddressAt A x.rem x.remA ∗
        memRegion (s.sp + 0x580#64) 48 ∗ memRegion (s.sp + 0x9b0#64) 24) ∗ F ∗ R) := by
    rw [stackAt_encSubStackV_split kit ikit hbound s.sp kit.storeShimStack
      (storeShimStack_le_encSubStackV_placed kit ikit)]
    exact Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hm4
  obtain ⟨u470, u478, hm5⟩ := memRegion16_exists_words2 (s.sp + 0x470#64) hm4'
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm5
  have hm6 : s2.mem ⊨ (((s2.sp + 0x470#64) ↦₆₄ u470) ∗ ((s2.sp + 0x478#64) ↦₆₄ u478) ∗
      ((0#64 + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.storePollOff))) ∗
      (((A.live box kit.storeBoxSize 8 ∗ kit.storeBoxAt box x.ssA x.remA (s.sp + 0x110#64) 0#8 ∗ A.pool ∗
        kit.storeAt x.ssA st0 ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xd0#64) ↦₆₄ x.ssA ∗ (s.sp + 0xd8#64) ↦₆₄ kit.ss_vt ∗
        ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (0#64 + kit.storeShimOff)) ∗
        ((0#64 + kit.storeFutVtOff) ↦₆₄ᵣ (0#64 + kit.storeFutDropOff)) ∗
        ((0#64 + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
        ((0#64 + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        sessionRecordAt A (s.sp + 0x110#64) g' rec' ∗ protocolAddressAt A x.rem x.remA ∗
        memRegion (s.sp + 0x580#64) 48 ∗ memRegion (s.sp + 0x9b0#64) 24) ∗ F) ∗ R) := by
    rw [hsp2]
    exact Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hm5
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := hsp2_al
  refine SegExitPlaced.of_sepWP hm6 (step_dfc_to_e10_placed hpc2 hrun2 hsp2_align rfl hx1_2) ?_
  rintro s3 P3 _ hsteps3 hpc3 hrun3 hm7
    ⟨rfl, hsp3, htr3, hx0_3, _, hx8_3, hx30_3, hx19_3, hx20_3, hx25_3, hx26_3, hx28_3, hx29_3, hvregs_3⟩
  rw [hsp2] at hsp3 hx8_3 hm7
  have hsp3_al : s3.spAligned = true :=
    CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hsp_al hsp3
  have hpref3 : s0.trace <+: s3.trace := by rw [htr3, htr2.2.2]; exact hpref1
  have hcrl3 : StoreKit.LibsignalCodeRoLoaded lsmpl s3.mem := hcrl2.of_keepsFrozen hsteps3.keepsFrozen
  let pollCall : StorePollCall × BitVec 64 × kit.StoreState :=
    (⟨box, s.sp + 0x580#64, ⟨x.remA, x.rem, s.sp + 0x110#64, g', rec'⟩⟩, x.ssA, st0)
  have hm8 : s3.mem ⊨ (kitStorePollPlacedSpec kit encRecord).pre pollCall s3 ∗
      ((((s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (0#64 + kit.storeFutVtOff) ∗
        A.live box kit.storeBoxSize 8 ∗
        memRegion (s.sp - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.storePollStack) ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xd0#64) ↦₆₄ x.ssA ∗ (s.sp + 0xd8#64) ↦₆₄ kit.ss_vt ∗
        ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (0#64 + kit.storeShimOff)) ∗
        ((0#64 + kit.storeFutVtOff) ↦₆₄ᵣ (0#64 + kit.storeFutDropOff)) ∗
        ((0#64 + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
        ((0#64 + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.storePollOff)) ∗
        memRegion (s.sp + 0x9b0#64) 24) ∗ F) ∗ R) := by
    dsimp only [kitStorePollPlacedSpec, pollCall]
    rw [hsp3]
    rw [stackAt_encSubStackV_split kit ikit hbound s.sp kit.storePollStack
      (storePollStack_le_encSubStackV_placed kit ikit)] at hm7
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_3, hx8_3, hrecOk, haddr⟩, Eq.mp (congrArg (s3.mem ⊨ ·) (by ac_rfl)) hm7⟩
  have henv3 : kit.envOk s3.fs.files :=
    (hfs.of_steps ((hsteps1.trans hsteps2).trans hsteps3)).envOk_at (evs := [])
      (by rw [htr3, htr2.2.2, htr1, List.append_nil]) (fun _ => NoFsEv.nil)
  refine call_rocl_alloc_placed (hEnv.kitOk.storePoll (by decide)) pollCall hpc3 hrun3 hsp3_al hx30_3 hpref3 hcrl3
    (withEnvPre_pre_intro (φ := fun s => kit.envOk s.fs.files) henv3 hm8) ?_
    (hR := entails_anyHeap_self_placed R)
  intro s4 hsteps4 hpc4 hrun4 hsp4 hsp4_al hcs4 hcrl4 hm9
  dsimp only [kitStorePollPlacedSpecE, withEnvPre, kitStorePollPlacedSpec, pollCall] at hm9
  rw [hsp3] at hsp4 hm9
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hm9
  obtain ⟨ans, ⟨hstoreRel, htr4⟩, hm9⟩ := hm9
  have hm9_poll : s4.mem ⊨
      storePollPlacedOutAt (s.sp + 0x580#64) ans ∗
      (memRegion (s.sp + 0x9b0#64) 24 ∗
      ((kit.storeBoxAt box x.ssA x.remA (s.sp + 0x110#64) 1#8 ∗
        kit.storeAt x.ssA (kit.storeUpdate st0 x.rem.val rec' ans) ∗
        (s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (0#64 + kit.storeFutVtOff) ∗
        A.live box kit.storeBoxSize 8 ∗
        protocolAddressAt A x.rem x.remA ∗ sessionRecordAt A (s.sp + 0x110#64) g' rec' ∗
        A.pool ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xd0#64) ↦₆₄ x.ssA ∗ (s.sp + 0xd8#64) ↦₆₄ kit.ss_vt ∗
        ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (0#64 + kit.storeShimOff)) ∗
        ((0#64 + kit.storeFutVtOff) ↦₆₄ᵣ (0#64 + kit.storeFutDropOff)) ∗
        ((0#64 + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
        ((0#64 + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.storePollOff))) ∗ F ∗ R)) := by
    rw [stackAt_encSubStackV_split kit ikit hbound s.sp kit.storePollStack
      (storePollStack_le_encSubStackV_placed kit ikit)]
    exact Eq.mp (congrArg (s4.mem ⊨ ·) (by ac_rfl)) hm9
  have hm10 := Satisfies.mono (sepConj_mono_left
    (storePollPlacedOut_words (s.sp + 0x580#64) ans)) hm9_poll
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hm10
  obtain ⟨w0, w1, w2, w3, w4, w5, H, ⟨hw0, hans, hH, hstaged⟩, hm10⟩ := hm10
  have hm10' : s4.mem ⊨ memRegion (s.sp + 0x9b0#64) 24 ∗
      (((s.sp + 0x580#64) ↦₆₄ w0 ∗ (s.sp + 0x580#64 + 8#64) ↦₆₄ w1 ∗
        (s.sp + 0x580#64 + 0x10#64) ↦₆₄ w2 ∗ (s.sp + 0x580#64 + 0x18#64) ↦₆₄ w3 ∗
        (s.sp + 0x580#64 + 0x20#64) ↦₆₄ w4 ∗ (s.sp + 0x580#64 + 0x28#64) ↦₆₄ w5 ∗ H ∗
        kit.storeBoxAt box x.ssA x.remA (s.sp + 0x110#64) 1#8 ∗
        kit.storeAt x.ssA (kit.storeUpdate st0 x.rem.val rec' ans) ∗
        (s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (0#64 + kit.storeFutVtOff) ∗
        A.live box kit.storeBoxSize 8 ∗
        protocolAddressAt A x.rem x.remA ∗ sessionRecordAt A (s.sp + 0x110#64) g' rec' ∗
        A.pool ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xd0#64) ↦₆₄ x.ssA ∗ (s.sp + 0xd8#64) ↦₆₄ kit.ss_vt ∗
        ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (0#64 + kit.storeShimOff)) ∗
        ((0#64 + kit.storeFutVtOff) ↦₆₄ᵣ (0#64 + kit.storeFutDropOff)) ∗
        ((0#64 + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
        ((0#64 + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.storePollOff))) ∗ F ∗ R) :=
    Eq.mp (congrArg (s4.mem ⊨ ·) (by ac_rfl)) hm10
  obtain ⟨u9b0, u9b8, u9c0, hm11⟩ := memRegion24_exists_words3 (s.sp + 0x9b0#64) hm10'
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm11
  have hm12 : s4.mem ⊨ (((s4.sp + 0x470#64) ↦₆₄ box) ∗ ((s4.sp + 0x478#64) ↦₆₄ (0#64 + kit.storeFutVtOff)) ∗
      ((s4.sp + 0x580#64) ↦₆₄ w0) ∗ ((s4.sp + 0x588#64) ↦₆₄ w1) ∗ ((s4.sp + 0x590#64) ↦₆₄ w2) ∗
      ((s4.sp + 0x598#64) ↦₆₄ w3) ∗ ((s4.sp + 0x5a0#64) ↦₆₄ w4) ∗ ((s4.sp + 0x5a8#64) ↦₆₄ w5) ∗
      ((s4.sp + 0x9b0#64) ↦₆₄ u9b0) ∗ ((s4.sp + 0x9b8#64) ↦₆₄ u9b8) ∗ ((s4.sp + 0x9c0#64) ↦₆₄ u9c0) ∗
      ((0#64 + kit.storeFutVtOff) ↦₆₄ᵣ (0#64 + kit.storeFutDropOff))) ∗
      (((H ∗ kit.storeBoxAt box x.ssA x.remA (s.sp + 0x110#64) 1#8 ∗
        kit.storeAt x.ssA (kit.storeUpdate st0 x.rem.val rec' ans) ∗
        A.live box kit.storeBoxSize 8 ∗
        protocolAddressAt A x.rem x.remA ∗ sessionRecordAt A (s.sp + 0x110#64) g' rec' ∗
        A.pool ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xd0#64) ↦₆₄ x.ssA ∗ (s.sp + 0xd8#64) ↦₆₄ kit.ss_vt ∗
        ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (0#64 + kit.storeShimOff)) ∗
        ((0#64 + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
        ((0#64 + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.storePollOff))) ∗ F) ∗ R) := by
    rw [hsp4]
    exact Eq.mp (congrArg (s4.mem ⊨ ·) (by ac_rfl)) hm11
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := hsp4_al
  have hx25_4 : s4.readReg64 .x25 = s4.sp + 0x580#64 := by
    rw [hsp4, cs_x25 hcs4, hx25_3, cs_x25 hcs2, hx25_1, hx25]
  refine SegExitPlaced.of_sepWP hm12
    (step_e14_to_e68_placed (kit.storeFutDrop_ne_zero (by decide)) hpc4 hrun4 hsp4_align hx25_4 hw0) ?_
  rintro s5 _ _ hsteps5 hpc5 hrun5 hm13
    ⟨rfl, hsp5, htr5, hx0_5, hx20_5, hx21_5, hx22_5, hx23_5, hx27_5, hx30_5,
      hx19_5, hx25_5, hx26_5, hx28_5, hx29_5, hvregs_5⟩
  rw [hsp4] at hsp5 hm13
  have hsp5_al : s5.spAligned = true :=
    CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hsp_al hsp5
  have hm14 : s5.mem ⊨ futDropSpec.pre () s5 ∗
      ((((s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (0#64 + kit.storeFutVtOff) ∗
        (s.sp + 0x580#64) ↦₆₄ w0 ∗ (s.sp + 0x588#64) ↦₆₄ w1 ∗ (s.sp + 0x590#64) ↦₆₄ w2 ∗
        (s.sp + 0x598#64) ↦₆₄ w3 ∗ (s.sp + 0x5a0#64) ↦₆₄ w4 ∗ (s.sp + 0x5a8#64) ↦₆₄ w5 ∗
        (s.sp + 0x9b0#64) ↦₆₄ w3 ∗ (s.sp + 0x9b8#64) ↦₆₄ w4 ∗ (s.sp + 0x9c0#64) ↦₆₄ w5 ∗
        ((0#64 + kit.storeFutVtOff) ↦₆₄ᵣ (0#64 + kit.storeFutDropOff))) ∗
      ((H ∗ kit.storeBoxAt box x.ssA x.remA (s.sp + 0x110#64) 1#8 ∗
        kit.storeAt x.ssA (kit.storeUpdate st0 x.rem.val rec' ans) ∗
        A.live box kit.storeBoxSize 8 ∗
        protocolAddressAt A x.rem x.remA ∗ sessionRecordAt A (s.sp + 0x110#64) g' rec' ∗
        A.pool ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xd0#64) ↦₆₄ x.ssA ∗ (s.sp + 0xd8#64) ↦₆₄ kit.ss_vt ∗
        ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (0#64 + kit.storeShimOff)) ∗
        ((0#64 + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
        ((0#64 + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.storePollOff))) ∗ F)) ∗ R) := by
    dsimp only [futDropSpec]
    rw [emp_sepConj]
    exact Eq.mp (congrArg (s5.mem ⊨ ·) (by ac_rfl)) hm13
  refine call_rocl_nopanic_placed (hEnv.kitOk.storeFutDrop (by decide)) ()
    hpc5 hrun5 hsp5_al hx30_5 (hcrl4.of_keepsFrozen hsteps5.keepsFrozen) hm14 ?_
  intro s6 hsteps6 hpc6 hrun6 hsp6 hsp6_al hcs6 hm15
  dsimp only [futDropSpec] at hm15
  rw [hsp5] at hsp6
  rw [satisfies_pure_sepConj] at hm15
  obtain ⟨htr6, hm15⟩ := hm15
  have hm15_box : s6.mem ⊨ kit.storeBoxAt box x.ssA x.remA (s.sp + 0x110#64) 1#8 ∗
      (((0#64 + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
      ((0#64 + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
      ((((s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (0#64 + kit.storeFutVtOff) ∗
        (s.sp + 0x580#64) ↦₆₄ w0 ∗ (s.sp + 0x588#64) ↦₆₄ w1 ∗ (s.sp + 0x590#64) ↦₆₄ w2 ∗
        (s.sp + 0x598#64) ↦₆₄ w3 ∗ (s.sp + 0x5a0#64) ↦₆₄ w4 ∗ (s.sp + 0x5a8#64) ↦₆₄ w5 ∗
        (s.sp + 0x9b0#64) ↦₆₄ w3 ∗ (s.sp + 0x9b8#64) ↦₆₄ w4 ∗ (s.sp + 0x9c0#64) ↦₆₄ w5 ∗
        ((0#64 + kit.storeFutVtOff) ↦₆₄ᵣ (0#64 + kit.storeFutDropOff)) ∗ H ∗
        A.live box kit.storeBoxSize 8 ∗
        kit.storeAt x.ssA (kit.storeUpdate st0 x.rem.val rec' ans) ∗
        protocolAddressAt A x.rem x.remA ∗ sessionRecordAt A (s.sp + 0x110#64) g' rec' ∗
        A.pool ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xd0#64) ↦₆₄ x.ssA ∗ (s.sp + 0xd8#64) ↦₆₄ kit.ss_vt ∗
        ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (0#64 + kit.storeShimOff)) ∗
        ((0#64 + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.storePollOff))) ∗ F) ∗ R)) :=
    Eq.mp (congrArg (s6.mem ⊨ ·) (by ac_rfl)) hm15
  have hm15_mem := Satisfies.mono (sepConj_mono_left
    (kit.storeBoxAt_memRegion box x.ssA x.remA (s.sp + 0x110#64) 1#8)) hm15_box
  have hm16 : s6.mem ⊨ (((0#64 + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
      ((0#64 + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64)) ∗
      ((((s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (0#64 + kit.storeFutVtOff) ∗
        (s.sp + 0x580#64) ↦₆₄ w0 ∗ (s.sp + 0x588#64) ↦₆₄ w1 ∗ (s.sp + 0x590#64) ↦₆₄ w2 ∗
        (s.sp + 0x598#64) ↦₆₄ w3 ∗ (s.sp + 0x5a0#64) ↦₆₄ w4 ∗ (s.sp + 0x5a8#64) ↦₆₄ w5 ∗
        (s.sp + 0x9b0#64) ↦₆₄ w3 ∗ (s.sp + 0x9b8#64) ↦₆₄ w4 ∗ (s.sp + 0x9c0#64) ↦₆₄ w5 ∗
        ((0#64 + kit.storeFutVtOff) ↦₆₄ᵣ (0#64 + kit.storeFutDropOff)) ∗ H ∗
        memRegion box kit.storeBoxSize ∗ A.live box kit.storeBoxSize 8 ∗
        kit.storeAt x.ssA (kit.storeUpdate st0 x.rem.val rec' ans) ∗
        protocolAddressAt A x.rem x.remA ∗ sessionRecordAt A (s.sp + 0x110#64) g' rec' ∗
        A.pool ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xd0#64) ↦₆₄ x.ssA ∗ (s.sp + 0xd8#64) ↦₆₄ kit.ss_vt ∗
        ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (0#64 + kit.storeShimOff)) ∗
        ((0#64 + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.storePollOff))) ∗ F) ∗ R) :=
    Eq.mp (congrArg (s6.mem ⊨ ·) (by ac_rfl)) hm15_mem
  have hx20_6 : s6.readReg64 .x20 = box := (cs_x20 hcs6).trans hx20_5
  have hx22_6 : s6.readReg64 .x22 = 0#64 + kit.storeFutVtOff := (cs_x22 hcs6).trans hx22_5
  refine SegExitPlaced.of_sepWP hm16
    (step_e6c_to_e7c_placed kit.storeBoxSize_ne_zero hpc6 hrun6 hx20_6 hx22_6) ?_
  rintro s7 P7 _ hsteps7 hpc7 hrun7 hm17
    ⟨rfl, hsp7, htr7, hx0_7, hx1_7, hx2_7, hx30_7,
      hx19_7, hx20_7, hx21_7, hx23_7, hx25_7, hx26_7, hx27_7, hx28_7, hx29_7, hvregs_7⟩
  rw [hsp6] at hsp7
  have hsp7_al : s7.spAligned = true :=
    CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hsp_al hsp7
  have hm18 : s7.mem ⊨ (rustDeallocSpec A).pre (box, kit.storeBoxSize, 8) s7 ∗
      (((storeVtablesAt kit ∗
        ((s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (0#64 + kit.storeFutVtOff)) ∗
        ((s.sp + 0x580#64) ↦₆₄ w0 ∗ (s.sp + 0x588#64) ↦₆₄ w1 ∗ (s.sp + 0x590#64) ↦₆₄ w2 ∗
          (s.sp + 0x598#64) ↦₆₄ w3 ∗ (s.sp + 0x5a0#64) ↦₆₄ w4 ∗ (s.sp + 0x5a8#64) ↦₆₄ w5) ∗
        (((s.sp + 0x9b0#64) ↦₆₄ w3) ∗ ((s.sp + 0x9b8#64) ↦₆₄ w4) ∗ ((s.sp + 0x9c0#64) ↦₆₄ w5)) ∗
        H ∗
        memRegion (s.sp - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - allocHookStack) ∗
        kit.storeAt x.ssA (kit.storeUpdate st0 x.rem.val rec' ans) ∗
        protocolAddressAt A x.rem x.remA ∗ sessionRecordAt A (s.sp + 0x110#64) g' rec' ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xd0#64) ↦₆₄ x.ssA ∗ (s.sp + 0xd8#64) ↦₆₄ kit.ss_vt) ∗ F) ∗ R) := by
    dsimp only [rustDeallocSpec, storeVtablesAt]
    rw [hsp7]
    rw [stackAt_encSubStackV_split kit ikit hbound s.sp allocHookStack
      (allocHookStack_le_encSubStackV_placed kit ikit)] at hm17
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_7, by rw [hx1_7, BitVec.toNat_ofNat, Nat.mod_eq_of_lt kit.storeBoxSize_lt],
      by rw [hx2_7]; rfl⟩,
      Eq.mp (congrArg (s7.mem ⊨ ·) (by ac_rfl)) hm17⟩
  rw [← h45_segExit_kitF_placed]
  refine call_nopanic_placed (dealloc_placed_ok_at_enc (h45_envF_placed hEnv)) (box, kit.storeBoxSize, 8)
    hpc7 hrun7 hsp7_al hx30_7 hm18 ?_
  intro s8 hsteps8 hpc8 hrun8 hsp8 hsp8_al hcs8 hm19
  rw [h45_segExit_kitF_placed]
  dsimp only [rustDeallocSpec] at hm19
  rw [hsp7] at hsp8 hm19
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm19
  obtain ⟨htr8, hm19⟩ := hm19
  have hm20 : s8.mem ⊨ storeVtablesAt kit ∗
      ((((s.sp + 0x470#64) ↦₆₄ box) ∗ ((s.sp + 0x470#64 + 8#64) ↦₆₄ (0#64 + kit.storeFutVtOff))) ∗
      (((s.sp + 0x580#64) ↦₆₄ w0) ∗ ((s.sp + 0x580#64 + 8#64) ↦₆₄ w1) ∗
        ((s.sp + 0x580#64 + 16#64) ↦₆₄ w2) ∗ ((s.sp + 0x580#64 + 24#64) ↦₆₄ w3) ∗
        ((s.sp + 0x580#64 + 32#64) ↦₆₄ w4) ∗ ((s.sp + 0x580#64 + 40#64) ↦₆₄ w5)) ∗
      ((storeBaseActive kit (kit.storeUpdate st0 x.rem.val rec' ans) ikit s.sp x g' rec' ∗
        (((s.sp + 0x9b0#64) ↦₆₄ w3) ∗ ((s.sp + 0x9b8#64) ↦₆₄ w4) ∗ ((s.sp + 0x9c0#64) ↦₆₄ w5)) ∗
        H) ∗ (F ∗ R))) := by
    dsimp only [storeBaseActive]
    rw [stackAt_encSubStackV_split kit ikit hbound s.sp allocHookStack
      (allocHookStack_le_encSubStackV_placed kit ikit)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Eq.mp (congrArg (s8.mem ⊨ ·) (by ac_rfl)) hm19
  have hm21 := Satisfies.mono (sepConj_mono
    (words2_entails_memRegion16 (s.sp + 0x470#64) box (0#64 + kit.storeFutVtOff))
    (sepConj_mono_left
      (words6_entails_memRegion48 (s.sp + 0x580#64) w0 w1 w2 w3 w4 w5)))
    (Satisfies.of_sep_right hm20)
  have hsteps_tail := hsteps5.trans (hsteps6.trans (hsteps7.trans hsteps8))
  have hcrl8 : StoreKit.LibsignalCodeRoLoaded lsmpl s8.mem := hcrl4.of_keepsFrozen hsteps_tail.keepsFrozen
  have hsteps_all := hsteps1.trans (hsteps2.trans (hsteps3.trans (hsteps4.trans hsteps_tail)))
  refine hcont s8 ans w0 w1 w2 w3 w4 w5 H hsteps_all hpc8 hrun8 hsp8 hsp8_al hcrl8
    (by rw [htr8, htr7, htr6, htr5, htr4, htr3, htr2.2.2, htr1])
    hstoreRel hH hstaged
    (by rw [cs_x19 hcs8, hx19_7, cs_x19 hcs6, hx19_5, cs_x19 hcs4, hx19_3, cs_x19 hcs2, hx19_1])
    (by rw [cs_x25 hcs8, hx25_7, cs_x25 hcs6, hx25_5, cs_x25 hcs4, hx25_3, cs_x25 hcs2, hx25_1])
    (by rw [cs_x26 hcs8, hx26_7, cs_x26 hcs6, hx26_5, cs_x26 hcs4, hx26_3, cs_x26 hcs2, hx26_1])
    (by rw [cs_x28 hcs8, hx28_7, cs_x28 hcs6, hx28_5, cs_x28 hcs4, hx28_3, cs_x28 hcs2, hx28_1])
    (by rw [cs_x29 hcs8, hx29_7, cs_x29 hcs6, hx29_5, cs_x29 hcs4, hx29_3, cs_x29 hcs2, hx29_1])
    (by rw [cs_vregs hcs8, hvregs_7, cs_vregs hcs6, hvregs_5,
            cs_vregs hcs4, hvregs_3, cs_vregs hcs2, hvregs_1])
    (by rw [cs_x27 hcs8, hx27_7, cs_x27 hcs6, hx27_5])
    (by rw [cs_x21 hcs8, hx21_7, cs_x21 hcs6, hx21_5])
    (by rw [cs_x23 hcs8, hx23_7, cs_x23 hcs6, hx23_5])
    hans
    (Eq.mp (congrArg (s8.mem ⊨ ·) (by ac_rfl)) hm21)

theorem h45_segApplyStore_placed_okVT [LibsignalPlacement] {F0 : SepProp}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hEnv : EncEnvTPlaced F0 kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord Hk)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
    (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64)
    (c : IdentityChange) (R : SepProp) (s0 s : State)
    (haddr : kit.addrOk x.rem.val)
    (hfs : EncFsCtxPlaced kit ikit Hk s0 s)
    (hap : ApplyStateVPlaced kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord x r sess otr taken k m otr' pqCap' pqPtr' c R s0 s) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s
      (fun s' => StoredStateVPlaced kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord x r sess otr taken k m otr' c R s0 s') := by
  let env := h45_envF_placed hEnv
  obtain ⟨⟨h15, htrust, hsave⟩, hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hcrl, hvregs⟩,
    htr, ⟨hx20, hx25, hx26, hx28⟩, hpt, hrest, hloc, hnow, hstk, hm⟩ := hap
  set sp := s0.sp - 0xbe0#64
  set draws := S.draws otr.pqrState x.rest
  set rec' := storedRecord sess otr' taken
  set ist2 := ikit.saveUpdate (ikit.trustUpdate ist0 x.rem.val k .sending (.ok true)) x.rem.val k (.ok c)
  have hsc_some : taken.senderChain.isSome = true :=
    fromSessionState_senderChain_isSome h15.2.2.1
  have hpref0 : s0.trace <+: s.trace := ⟨_, htr.symm⟩
  have hx25' : s.readReg64 .x25 = s.sp + 0x580#64 := by rw [hsp]; exact hx25
  have hm_in : s.mem ⊨
      (cmSlots A s.sp sess taken otr' pqCap' pqPtr' k m ∗ cmScratch s.sp ∗
        encSpillsAtV kit.ss_vt ikit.id_vt s.sp x ∗ memRegion (s.sp + 0x46a#64) 0x716 ∗
        memRegion x.ret 248 ∗ encCommonPlaced A ctl x draws s0) ∗
      (encStoreExtraPlaced kit st0 ikit ist2 x s0 ∗ R) := by
    rw [hsp]
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm
  rw [← h45_segExit_kitF_placed]
  refine apply_to_de8_placed env (sepConj_mono_left (entails_anyHeap _))
    hpc hrun hsp hsp_al hcrl hx25' hpref0 hsc_some hm_in ?_
  intro s_de8 g' hsteps_de8 hpc_de8 hrun_de8 hsp_de8 hsp_de8_al hcrl_de8 htr_de8
    hx19_de8 hx20_de8 hx25_de8 hx26_de8 hx28_de8 hx29_de8 hvregs_de8 hm_de8
  rw [h45_segExit_kitF_placed]
  have hsp_de8' : s_de8.sp = sp := hsp_de8.trans hsp
  have hsp_de8_s0 : s_de8.sp = s0.sp - 0xbe0#64 := hsp_de8'
  have hpref_de8 : s0.trace <+: s_de8.trace := by rw [htr_de8]; exact hpref0
  set F := storePassivePlaced kit ikit ist2 ctl x k m draws s0
  have hm_de8' : s_de8.mem ⊨
      (((sessionRecordAt A (s.sp + 0x110#64) g' rec' ∗
        ((s.sp + 0x280#64) ↦₆₄ (s.sp + 0x128#64)) ∗ memRegion (s.sp + 0x288#64) 200 ∗
        ((s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
        apiEncResultAt A (s.sp + 0x370#64) (.ok m) ∗
        ((s.sp + 0x468#64) ↦₈ 0#8) ∗ ((s.sp + 0x469#64) ↦₈ 0#8)) ∗
      cmScratch s.sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt s.sp x ∗
      memRegion (s.sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
      encCommonPlaced A ctl x draws s0) ∗ encStoreExtraPlaced kit st0 ikit ist2 x s0) ∗ R :=
    Eq.mp (congrArg (s_de8.mem ⊨ ·) (by ac_rfl)) hm_de8
  have hm_split := Satisfies.mono
    (sepConj_mono_left (store_mem_split_placed kit st0 ikit ist2 ctl x g' rec' k m draws s0 s.sp hsp))
    hm_de8'
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_split
  rcases hm_split with ⟨hbound, hm_split⟩
  have hm_store_in : s_de8.mem ⊨ (storeVtablesAt kit ∗
      storeBaseActive kit st0 ikit s_de8.sp x g' rec' ∗
      memRegion (s_de8.sp + 0x470#64) 16 ∗ memRegion (s_de8.sp + 0x580#64) 48 ∗
      memRegion (s_de8.sp + 0x9b0#64) 24) ∗ (F ∗ R) := by
    rw [hsp_de8]
    have hm_vt := storeVtablesAt_placed_intro hEnv.vtables hcrl_de8.2 hm_split
    dsimp only [F]
    exact Eq.mp (congrArg (s_de8.mem ⊨ ·) (by ac_rfl)) hm_vt
  have hx20_de8' : s_de8.readReg64 .x20 = s_de8.sp + 0x58#64 := by
    rw [hx20_de8, hsp_de8, hsp, hx20]
  have hx25_de8' : s_de8.readReg64 .x25 = s_de8.sp + 0x580#64 := by
    rw [hx25_de8, hsp_de8, hx25']
  have hrecOk : kit.RecOk rec' := hEnv.recOk haddr h15
  have hfs_de8 : FsCtx kit.envOk True (lsProg_464 Hk) s_de8 s_de8 :=
    ((hfs.of_steps hsteps_de8).rebase (by rw [htr_de8, htr])
      (fun hQ => by
        obtain ⟨⟨hl, -⟩, ht, hs⟩ := hQ
        simp only [NoFsEv.append_iff, hl, ht, hs, and_self])).mono
      (fun _ h => h.1) (fun _ => trivial)
  refine h45_store_to_e80_placed hEnv hrecOk haddr hbound hpc_de8 hrun_de8 hsp_de8_al
    hx20_de8' hx25_de8' hpref_de8 hcrl_de8 hfs_de8 hm_store_in ?_
  intro sm ans w0 w1 w2 w3 w4 w5 H _hsteps_e80 hpcm hrunm hspm hspm_al hcrlm htrm hstoreRel hH hstaged
    hx19m hx25m hx26m hx28m hx29m hvregsm hx27m hx21m hx23m hans hmm
  have hspm' : sm.sp = sp := hspm.trans hsp_de8'
  have htrm' : sm.trace = s0.trace ++
      (kit.loadEvs encRecord x.rem.val (.ok (some r)) ++
        (ikit.trustEvs x.rem.val k .sending (.ok true) ++
          ikit.saveEvs x.rem.val k (.ok c)) ++
        kit.storeEvs encRecord x.rem.val rec' ans) := by
    rw [htrm, htr_de8, htr]
    simp only [List.append_assoc]
  rcases ans with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
  ·
    dsimp only [pollTag] at hans
    subst hans
    obtain ⟨rfl, rfl, rfl⟩ := hstaged rfl
    have hmm_emp : sm.mem ⊨ emp ∗
        (((storeBaseActive kit (kit.storeUpdate st0 x.rem.val rec' (.error ())) ikit s_de8.sp x g' rec' ∗
          memRegion (s_de8.sp + 0x470#64) 16 ∗ memRegion (s_de8.sp + 0x580#64) 48 ∗
          (((s_de8.sp + 0x9b0#64) ↦₆₄ 1#64) ∗ ((s_de8.sp + 0x9b8#64) ↦₆₄ w4) ∗
            ((s_de8.sp + 0x9c0#64) ↦₆₄ w5)) ∗
          (w1 ↦ᵣ storeHookStr)) ∗ F) ∗ R) := by
      rw [emp_sepConj, sepConj_assoc]
      exact hmm
    refine SegExitPlaced.of_sepWP hmm_emp (step_e80_err_placed hpcm hrunm hx27m) ?_
    rintro s_err _ _ hsteps_err hpc_err hrun_err hm_err
      ⟨rfl, hsp_err, htr_err, hx19_err, hx21_err, hx23_err, hx26_err, hx27_err, hx28_err, hx29_err, hvregs_err⟩
    rw [emp_sepConj] at hm_err
    have hcrl_err : StoreKit.LibsignalCodeRoLoaded lsmpl s_err.mem := hcrlm.of_keepsFrozen hsteps_err.keepsFrozen
    have hm_ro' : s_err.mem ⊨
        ((storeBaseActive kit (kit.storeUpdate st0 x.rem.val rec' (.error ())) ikit s_de8.sp x g' rec' ∗
          memRegion (s_de8.sp + 0x470#64) 16 ∗ memRegion (s_de8.sp + 0x580#64) 48 ∗
          (((s_de8.sp + 0x9b0#64) ↦₆₄ 1#64) ∗ ((s_de8.sp + 0x9b8#64) ↦₆₄ w4) ∗
            ((s_de8.sp + 0x9c0#64) ↦₆₄ w5)) ∗
          (w1 ↦ᵣ storeHookStr)) ∗ F) ∗ R :=
      hm_err
    have htail_ent := store_mem_to_tail_placed kit (kit.storeUpdate st0 x.rem.val rec' (.error ()))
      ikit ist2 ctl x g' rec' k m draws s0 s_de8.sp hsp_de8' hbound 1#64 w4 w5
      (w1 ↦ᵣ storeHookStr)
    have hm_tail := Satisfies.mono (sepConj_mono_left htail_ent) hm_ro'
    have htm : Tails.TailModel (h45_kitF_placed kit) st0 ikit ist0 C S uuidTryParse encRecord x
        (answersOfStoreErr r c) (.error (.store ())) s0 s_err :=
      (h45_tailModel_kitF_placed kit st0 ikit ist0 C S uuidTryParse encRecord x
        (answersOfStoreErr r c) (.error (.store ())) s0 s_err).mpr
        (StepsThroughEncrypt.tailModel_store_err c (encRecord := encRecord) (s0 := s0) (s := s_err)
          h15 htrust hsave hstoreRel (htr_err.trans htrm'))
    have hdraws : x.draws S (answersOfStoreErr r c) = draws :=
      StepsThroughEncrypt.draws_eq h15 (answersOfStoreErr r c) rfl
    have hfinal :
        (h45_kitF_placed kit).storeFinal st0 (answersOfStoreErr r c) (x.model C S uuidTryParse (answersOfStoreErr r c)).2 =
          kit.storeUpdate st0 x.rem.val rec' (.error ()) := by
      rw [h45_storeFinal_kitF_placed, StepsThroughEncrypt.model_store_err c h15]; rfl
    have hid_final :
        ikit.idFinal ist0 (answersOfStoreErr r c) (x.model C S uuidTryParse (answersOfStoreErr r c)).2 =
          ist2 := by
      rw [StepsThroughEncrypt.model_store_err c h15]; rfl
    rw [← h45_segExit_kitF_placed]
    refine SegExitPlaced.of_false
      (tailStoreHookErr_placed_ok env x R s0 s_err (answersOfStoreErr r c) (.store ())
        0x800000000000001A#64 w1 10#64 1#64 w4 w5
        (w1 ↦ᵣ storeHookStr) cmScratch (Or.inr rfl)
        g' rec' none m 0xf2c 0x9b0 (Or.inr (Or.inr rfl))
        htm (speStaged_storeErr_placed A x.ret w1 w4 w5) ?_)
    refine ⟨hpc_err,
      ⟨hrun_err, hsp_err.trans hspm', hsp0_al,
       CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hspm_al hsp_err,
       by rw [hx29_err, hx29m, hx29_de8, hx29],
       by rw [hx19_err, hx19m, hx19_de8, hx19], hcrl_err,
       by rw [hvregs_err, hvregsm, hvregs_de8, hvregs]⟩,
      ⟨by rw [hx26_err, hx26m, hx26_de8, hx26], by rw [hx28_err, hx28m, hx28_de8, hx28],
       by rw [hx27_err, hx27m], by rw [hx21_err, hx21m], by rw [hx23_err, hx23m]⟩,
      hstk, ?_⟩
    dsimp only
    rw [hdraws, hfinal, hid_final, ← hsp_de8_s0]
    exact Eq.mp (congrArg (s_err.mem ⊨ ·) (by ac_rfl)) hm_tail
  ·
    dsimp only [pollTag] at hans
    subst hans
    rw [hH rfl, sepConj_emp] at hmm
    have hmm_emp : sm.mem ⊨ emp ∗
        (((storeBaseActive kit (kit.storeUpdate st0 x.rem.val rec' (.ok ())) ikit s_de8.sp x g' rec' ∗
          memRegion (s_de8.sp + 0x470#64) 16 ∗ memRegion (s_de8.sp + 0x580#64) 48 ∗
          (((s_de8.sp + 0x9b0#64) ↦₆₄ w3) ∗ ((s_de8.sp + 0x9b8#64) ↦₆₄ w4) ∗
            ((s_de8.sp + 0x9c0#64) ↦₆₄ w5))) ∗ F) ∗ R) := by
      rw [emp_sepConj, sepConj_assoc]
      exact hmm
    refine SegExitPlaced.of_sepWP hmm_emp (step_e80_ok_placed hpcm hrunm hx27m) ?_
    rintro s_ok _ _ hsteps_ok hpc_ok hrun_ok hm_ok
      ⟨rfl, hsp_ok, htr_ok, hx19_ok, hx26_ok, hx28_ok, hx29_ok, hvregs_ok⟩
    rw [emp_sepConj] at hm_ok
    have hcrl_ok : StoreKit.LibsignalCodeRoLoaded lsmpl s_ok.mem := hcrlm.of_keepsFrozen hsteps_ok.keepsFrozen
    have hm_ok_9b0 : s_ok.mem ⊨
        (((s_de8.sp + 0x9b0#64) ↦₆₄ w3) ∗ ((s_de8.sp + 0x9b0#64 + 8#64) ↦₆₄ w4) ∗
          ((s_de8.sp + 0x9b0#64 + 16#64) ↦₆₄ w5)) ∗
        ((storeBaseActive kit (kit.storeUpdate st0 x.rem.val rec' (.ok ())) ikit s_de8.sp x g' rec' ∗
          memRegion (s_de8.sp + 0x470#64) 16 ∗ memRegion (s_de8.sp + 0x580#64) 48) ∗ F ∗ R) := by
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact Eq.mp (congrArg (s_ok.mem ⊨ ·) (by ac_rfl)) hm_ok
    have hm_ok_fold := Satisfies.mono (sepConj_mono_left
      (words3_entails_memRegion24 (s_de8.sp + 0x9b0#64) w3 w4 w5)) hm_ok_9b0
    have hm_ok_pre : s_ok.mem ⊨
        ((storeBaseActive kit (kit.storeUpdate st0 x.rem.val rec' (.ok ())) ikit s_de8.sp x g' rec' ∗
          memRegion (s_de8.sp + 0x470#64) 16 ∗ memRegion (s_de8.sp + 0x580#64) 48 ∗
          memRegion (s_de8.sp + 0x9b0#64) 24) ∗
          storePassivePlaced kit ikit ist2 ctl x k m draws s0) ∗ R := by
      dsimp only [F] at hm_ok_fold
      exact Eq.mp (congrArg (s_ok.mem ⊨ ·) (by ac_rfl)) hm_ok_fold
    have hm_ok_stored := Satisfies.mono (sepConj_mono_left
      (store_mem_to_stored_placed kit (kit.storeUpdate st0 x.rem.val rec' (.ok ()))
        ikit ist2 ctl x g' rec' k m draws s0 s_de8.sp hsp_de8' hbound)) hm_ok_pre
    refine SegExitPlaced.next ⟨⟨h15, htrust, hsave, hstoreRel⟩, hpc_ok,
      ⟨hrun_ok, hsp_ok.trans hspm', hsp0_al,
        CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hspm_al hsp_ok,
        by rw [hx29_ok, hx29m, hx29_de8, hx29],
        by rw [hx19_ok, hx19m, hx19_de8, hx19], hcrl_ok,
        by rw [hvregs_ok, hvregsm, hvregs_de8, hvregs]⟩,
      by rw [htr_ok, htrm']; simp only [List.append_assoc]; rfl,
      ⟨by rw [hx26_ok, hx26m, hx26_de8, hx26],
       by rw [hx28_ok, hx28m, hx28_de8, hx28]⟩,
      hpt, hrest, hloc, hnow, hstk, ?_⟩
    dsimp only
    rw [← hsp_de8_s0]
    exact Eq.mp (congrArg (s_ok.mem ⊨ ·) (by ac_rfl)) hm_ok_stored

end SegApplyStore

end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt

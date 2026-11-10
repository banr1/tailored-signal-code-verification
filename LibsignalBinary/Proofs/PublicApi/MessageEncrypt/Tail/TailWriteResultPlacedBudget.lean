/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PlacedDefsBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.CommonPlacedBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailWriteResultPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Budget-Threaded Relocatable `T2` Result Writer and Epilogue (`+0x5f8..+0x660`)

Steps `+0x5f8..+0x660` (`ret`) on Block `198` (`lsProg_198 H`), closes `SeamBudget ... FreeOnlyEvs`
at `[]`, and establishes `PlacedDefsBudget.SegExitPlaced`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailWriteResultPlacedBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget (SpqrSendBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PlacedDefsBudget
  (EncEnvPlaced SegExitPlaced WithStoresEncEnv withStoresEncPlacedSpecV)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.CommonPlacedBudget
  (EncTailVPlaced encTail_mem_retag_eq)
open CryptoGames.LibsignalSession (Crypto)
open CryptoGames.LibsignalSessionApi (ApiError CiphertextMessage SessionRecord StoreAnswers)
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser protocolAddressAt tapeAfter)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal apiEncResultAt)
open CryptoVerification.LibsignalPublicApi.Placed (lsProg_198)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (IdentityStoreSpec SessionStoreSpec withLsCodeRoLoaded)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
  (WithStoresEncGhost encCommonPlaced encEntryPlaced encSavedRegs encSpillsAtV encStoreExtraPlaced
   encSubStack nowAt withStoresEncStack withStoresEncStackV withStoresEncStack_join_extra_placed)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon
  (ResStaged TailModel exists_unpack64List words64At words64At_eq_pointsToBytes
   writeResult_frame_entails_stackAtV)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteResult
  (encSavedRegsAtSp encSavedRegs_eq_atSp memRegion_eq_exists_words64At words64At_27 words64At_4)

set_option maxRecDepth 200000

private theorem bv_sub_add_lit_local (x a b : BitVec 64) : x - a + b = x - (a - b) := by
  bv_omega

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit_local BitVec.toNat_zero

private theorem protocolAddressAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    protocolAddressAt (A.atState lim st s) = protocolAddressAt A.repAlloc := rfl

set_option maxHeartbeats 800000 in
theorem writeResult_placed_sepWP [LibsignalPlacement] {H : LibsignalHooks}
    {sp ret : BitVec 64} {w0 w1 w2 w3 : BitVec 64}
    {bws rws4 rws27 : List (BitVec 64)} {s0 s : State}
    (hbws : bws.length = 27) (hr4 : rws4.length = 4) (hr27 : rws27.length = 27)
    (hpc : s.pc = encEntryPlaced + 0x5f8#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp)
    (hx19 : s.readReg64 .x19 = ret)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64)
    (hx22 : s.readReg64 .x22 = w0)
    (hx27 : s.readReg64 .x27 = w1)
    (hx21 : s.readReg64 .x21 = w2)
    (hx23 : s.readReg64 .x23 = w3) :
    SepWP (lsProg_198 H) (s0.readReg64 .lr) s
      (words64At (sp + 0x4a0#64) bws ∗ words64At ret rws4 ∗
        words64At (ret + 0x20#64) rws27 ∗ encSavedRegsAtSp sp s0)
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = sp + 0xbe0#64 ∧
        sf.trace = s.trace ∧
        (sf.readReg64 .x19 = s0.readReg64 .x19 ∧
         sf.readReg64 .x20 = s0.readReg64 .x20 ∧
         sf.readReg64 .x21 = s0.readReg64 .x21 ∧
         sf.readReg64 .x22 = s0.readReg64 .x22 ∧
         sf.readReg64 .x23 = s0.readReg64 .x23 ∧
         sf.readReg64 .x24 = s0.readReg64 .x24 ∧
         sf.readReg64 .x25 = s0.readReg64 .x25 ∧
         sf.readReg64 .x26 = s0.readReg64 .x26 ∧
         sf.readReg64 .x27 = s0.readReg64 .x27 ∧
         sf.readReg64 .x28 = s0.readReg64 .x28 ∧
         sf.readReg64 .x29 = s0.readReg64 .x29 ∧
         calleeSavedVRegs sf = calleeSavedVRegs s) ∧
        P_f = (words64At (sp + 0x4a0#64) bws ∗ words64At ret [w0, w1, w2, w3] ∗
          words64At (ret + 0x20#64) bws ∗ encSavedRegsAtSp sp s0)) := by
  subst hsp
  unfold encEntryPlaced at hpc
  dsimp only [lsProg_198, ite_true]
  by_vm_steps (
    rw [words64At_27 (s.sp + 0x4a0#64) hbws,
        words64At_4 ret hr4,
        words64At_27 (ret + 0x20#64) hr27]
    unfold encSavedRegsAtSp
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun)
    refine ⟨by simp only [wp_norm, arm64_norm], rfl, rfl,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    rw [words64At_27 (ret + 0x20#64) hbws]
    simp only [words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc])

theorem tailWriteResult_placed_ok_core [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64} {parse : UuidParser}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (x : WithStoresEncGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit)
    (res : Except (ApiError AddrVal Unit) CiphertextMessage) (w0 w1 w2 w3 : BitVec 64)
    (bs : List (BitVec 8)) (H : SepProp)
    (hm : TailModel kit st0 ikit ist0 C S parse encRecord x answers res s0 s)
    (hst : ResStaged A.repAlloc x.ret res [w0, w1, w2, w3] bs H)
    (hs : EncTailVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
      x st_init st answers (encEntryPlaced + 0x5f8#64)
      (fun sp s => s.readReg64 .x28 = sp + 0x4a0#64 ∧ s.readReg64 .x22 = w0 ∧
        s.readReg64 .x27 = w1 ∧ s.readReg64 .x21 = w2 ∧ s.readReg64 .x23 = w3)
      (fun sp => memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x390 ∗ ((sp + 0x4a0#64) ↦ₛ bs) ∗
        memRegion (sp + 0x578#64) 0x608 ∗ H)
      R s0 s) :
    SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord Hk
      x st_init R s0 s (fun _ => False) := by
  rcases hm with ⟨⟨hmod_res, hcallsRel, hidCallsRel⟩, htrace⟩
  rcases hst with ⟨hres_np, _, hbs_len, hres_ent⟩
  rcases hs with ⟨hbud, hpc, ⟨hrun, hsp, _hsp0_al, hsp_al, _hx29, hx19, _hcrl, hvregs⟩,
    ⟨hx28, hx22, hx27, hx21, hx23⟩, _hstack_le, hmem⟩
  have hmem := Eq.mp (congrArg (s.mem ⊨ ·)
    (encTail_mem_retag_eq kit st0 ikit ist0 C ctl parse S x answers _ R s0)) hmem
  obtain ⟨bws, hbws, hbs_eq⟩ := exists_unpack64List 27 (by omega : bs.length = 8 * 27)
  have hbs_words : ∀ a : BitVec 64, (a ↦ₛ bs) = words64At a bws := fun a => by
    rw [hbs_eq, ← words64At_eq_pointsToBytes]
  let sp := s0.sp - 0xbe0#64
  let stf := kit.storeFinal st0 answers (x.model C S parse answers).2
  let istf := ikit.idFinal ist0 answers (x.model C S parse answers).2
  let R' := encStoreExtraPlaced kit stf ikit istf x s0 ∗ R
  change s.mem ⊨
    (memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x390 ∗ ((sp + 0x4a0#64) ↦ₛ bs) ∗
      memRegion (sp + 0x578#64) 0x608 ∗ H) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R' at hmem
  have hret_split : memRegion x.ret 248 =
      memRegion x.ret (8 * 4) ∗ memRegion (x.ret + 0x20#64) (8 * 27) :=
    memRegion_split' (b := x.ret) (b' := x.ret + 0x20#64) (n := 8 * 4) (k := 8 * 27)
      (by decide) rfl (by decide)
  let F := memRegion sp 0x58 ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion (sp + 0x110#64) 0x390 ∗
    memRegion (sp + 0x578#64) 0x608 ∗ H ∗ stackAt sp encSubStack ∗
    (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
    protocolAddressAt A.repAlloc x.loc x.locA ∗
    nowAt s0.sp x.now ∗ tapeAfter ctl x.cur x.rest (x.draws S answers) ∗
    lsLogOff ∗ A.pool lim st s
  have hmem1 : s.mem ⊨ memRegion x.ret (8 * 4) ∗ (memRegion (x.ret + 0x20#64) (8 * 27) ∗
      words64At (sp + 0x4a0#64) bws ∗ encSavedRegsAtSp sp s0 ∗ (F ∗ R')) := by
    have heq :
      ((memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x390 ∗ ((sp + 0x4a0#64) ↦ₛ bs) ∗
        memRegion (sp + 0x578#64) 0x608 ∗ H) ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
      encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R') =
      (memRegion x.ret (8 * 4) ∗ (memRegion (x.ret + 0x20#64) (8 * 27) ∗
      words64At (sp + 0x4a0#64) bws ∗ encSavedRegsAtSp sp s0 ∗ (F ∗ R'))) := by
      unfold encCommonPlaced
      rw [protocolAddressAt_atState]
      dsimp only [F, sp, RustCliAllocBudget.atState]
      rw [hbs_words (s0.sp - 0xbe0#64 + 0x4a0#64), hret_split, encSavedRegs_eq_atSp s0.sp s0]
      sep_ac_rfl
    rwa [← heq]
  obtain ⟨rws4, hr4, hmem2⟩ := memRegion_eq_exists_words64At 4 x.ret (by decide) s.mem _ hmem1
  rw [← sepConj_assoc, sepConj_comm (words64At x.ret rws4), sepConj_assoc] at hmem2
  obtain ⟨rws27, hr27, hmem3⟩ :=
    memRegion_eq_exists_words64At 27 (x.ret + 0x20#64) (by decide) s.mem _ hmem2
  have hmem4 : s.mem ⊨
      (words64At (sp + 0x4a0#64) bws ∗ words64At x.ret rws4 ∗
        words64At (x.ret + 0x20#64) rws27 ∗ encSavedRegsAtSp sp s0) ∗ (F ∗ R') := by
    have heq :
      (words64At (x.ret + 0x20#64) rws27 ∗ words64At x.ret rws4 ∗
        words64At (sp + 0x4a0#64) bws ∗ encSavedRegsAtSp sp s0 ∗ (F ∗ R')) =
      ((words64At (sp + 0x4a0#64) bws ∗ words64At x.ret rws4 ∗
        words64At (x.ret + 0x20#64) rws27 ∗ encSavedRegsAtSp sp s0) ∗ (F ∗ R')) := by sep_ac_rfl
    rwa [← heq]
  intro hL
  have hwp := writeResult_placed_sepWP (H := Hk) (s0 := s0)
    hbws hr4 hr27 hpc hrun hsp_al hsp hx19 hx28 hx22 hx27 hx21 hx23
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, hvmf, hspf, htracef, hcsf, rfl⟩ | ⟨_, _hoom⟩⟩ :=
    hwp.elim hmem4 hL
  rotate_left
  · exact (not_satisfies_false_sepConj _hoom).elim
  rw [hvregs] at hcsf
  have hspf0 : sf.sp = s0.sp := by
    rw [hspf]; bv_omega
  obtain ⟨evs_tot, hst_tot, hevs_tot⟩ := hbud.finish FreeOnlyEvs.nil
  have hst_tot' : st = M.stepEvents evs_tot st_init := hst_tot
  have hpool_eq : A.pool lim st s = A.pool lim (M.stepEvents evs_tot st_init) sf := by
    rw [← A.pool_transport lim st s sf hvmf, ← hst_tot']
  refine ⟨sf, hsteps, Or.inr (Or.inl ⟨⟨hpcf, hspf0, hrunf⟩, ⟨hspf0, hcsf⟩, ?_⟩)⟩
  let PostBody :=
    kit.storeAt x.ssA stf ∗
    ikit.identityAt x.idA istf ∗
    apiEncResultAt A.repAlloc x.ret (x.model C S parse answers).1 ∗
    nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
    protocolAddressAt A.repAlloc x.loc x.locA ∗ tapeAfter ctl x.cur x.rest (x.draws S answers) ∗
    lsLogOff ∗ stackAt s0.sp (withStoresEncStackV kit ikit) ∗
    A.pool lim (M.stepEvents evs_tot st_init) sf
  have hmf1 : sf.mem ⊨
      ((words64At x.ret [w0, w1, w2, w3] ∗ ((x.ret + 0x20#64) ↦ₛ bs) ∗ H) ∗
       (memRegion sp 0x58 ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion (sp + 0x110#64) 0x390 ∗
        ((sp + 0x4a0#64) ↦ₛ bs) ∗ memRegion (sp + 0x578#64) 0x608 ∗
        encSavedRegs s0.sp s0 ∗ stackAt sp encSubStack) ∗
       (nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
        protocolAddressAt A.repAlloc x.loc x.locA ∗ tapeAfter ctl x.cur x.rest (x.draws S answers) ∗
        lsLogOff ∗ A.pool lim (M.stepEvents evs_tot st_init) sf)) ∗ R' := by
    have heq :
      ((words64At (sp + 0x4a0#64) bws ∗ words64At x.ret [w0, w1, w2, w3] ∗
        words64At (x.ret + 0x20#64) bws ∗ encSavedRegsAtSp sp s0) ∗ (F ∗ R')) =
      (((words64At x.ret [w0, w1, w2, w3] ∗ ((x.ret + 0x20#64) ↦ₛ bs) ∗ H) ∗
       (memRegion sp 0x58 ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion (sp + 0x110#64) 0x390 ∗
        ((sp + 0x4a0#64) ↦ₛ bs) ∗ memRegion (sp + 0x578#64) 0x608 ∗
        encSavedRegs s0.sp s0 ∗ stackAt sp encSubStack) ∗
       (nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
        protocolAddressAt A.repAlloc x.loc x.locA ∗ tapeAfter ctl x.cur x.rest (x.draws S answers) ∗
        lsLogOff ∗ A.pool lim (M.stepEvents evs_tot st_init) sf)) ∗ R') := by
      dsimp only [F, sp]
      rw [hpool_eq, ← hbs_words (s0.sp - 0xbe0#64 + 0x4a0#64), ← hbs_words (x.ret + 0x20#64),
          ← encSavedRegs_eq_atSp s0.sp s0]
      sep_ac_rfl
    rwa [← heq]
  have hstack_ent := writeResult_frame_entails_stackAtV kit.ss_vt ikit.id_vt x s0 bs hbs_len
  have hres_ent' :
      words64At x.ret [w0, w1, w2, w3] ∗ ((x.ret + 0x20#64) ↦ₛ bs) ∗ H ⊢
        apiEncResultAt A.repAlloc x.ret (x.model C S parse answers).1 := by
    rw [hmod_res]; exact hres_ent
  have hmf2 := Satisfies.mono
    (sepConj_mono_left (sepConj_mono hres_ent' (sepConj_mono_left hstack_ent))) hmf1
  have hmf2' : sf.mem ⊨
      (encStoreExtraPlaced kit stf ikit istf x s0 ∗ stackAt s0.sp withStoresEncStack) ∗
      (apiEncResultAt A.repAlloc x.ret (x.model C S parse answers).1 ∗
       nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
       protocolAddressAt A.repAlloc x.loc x.locA ∗ tapeAfter ctl x.cur x.rest (x.draws S answers) ∗
       lsLogOff ∗ A.pool lim (M.stepEvents evs_tot st_init) sf) ∗ R := by
    have heq :
      ((apiEncResultAt A.repAlloc x.ret (x.model C S parse answers).1 ∗
        stackAt s0.sp withStoresEncStack ∗
        (nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
         protocolAddressAt A.repAlloc x.loc x.locA ∗ tapeAfter ctl x.cur x.rest (x.draws S answers) ∗
         lsLogOff ∗ A.pool lim (M.stepEvents evs_tot st_init) sf)) ∗ R') =
      ((encStoreExtraPlaced kit stf ikit istf x s0 ∗ stackAt s0.sp withStoresEncStack) ∗
       (apiEncResultAt A.repAlloc x.ret (x.model C S parse answers).1 ∗
        nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
        protocolAddressAt A.repAlloc x.loc x.locA ∗ tapeAfter ctl x.cur x.rest (x.draws S answers) ∗
        lsLogOff ∗ A.pool lim (M.stepEvents evs_tot st_init) sf) ∗ R) := by
      dsimp only [R']; sep_ac_rfl
    rwa [← heq]
  have hmf2'' := Satisfies.mono
    (sepConj_mono_left (withStoresEncStack_join_extra_placed kit stf ikit istf x s0)) hmf2'
  have hmf3 : sf.mem ⊨ PostBody ∗ R := by
    have heq :
      ((kit.storeAt x.ssA stf ∗ ikit.identityAt x.idA istf ∗
        stackAt s0.sp (withStoresEncStackV kit ikit)) ∗
       (apiEncResultAt A.repAlloc x.ret (x.model C S parse answers).1 ∗
        nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
        protocolAddressAt A.repAlloc x.loc x.locA ∗ tapeAfter ctl x.cur x.rest (x.draws S answers) ∗
        lsLogOff ∗ A.pool lim (M.stepEvents evs_tot st_init) sf) ∗ R) =
      (PostBody ∗ R) := by
      dsimp only [PostBody]; sep_ac_rfl
    rwa [← heq]
  have hpure : (x.model C S parse answers).1 ≠ .error .panic ∧
      kit.callsRel st0 answers (x.model C S parse answers).2 ∧
      ikit.idCallsRel ist0 answers (x.model C S parse answers).2 ∧
      sf.trace = s0.trace ++ ikit.traceOfWith kit encRecord answers (x.model C S parse answers).2 ∧
      WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv parse x evs_tot :=
    ⟨hmod_res ▸ hres_np, hcallsRel, hidCallsRel, htracef.trans htrace, hevs_tot⟩
  have hmf4 : sf.mem ⊨
      (⌜(x.model C S parse answers).1 ≠ .error .panic ∧
        kit.callsRel st0 answers (x.model C S parse answers).2 ∧
        ikit.idCallsRel ist0 answers (x.model C S parse answers).2 ∧
        sf.trace = s0.trace ++ ikit.traceOfWith kit encRecord answers (x.model C S parse answers).2 ∧
        WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv parse x evs_tot⌝ ∗
       PostBody) ∗ R := by
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, hmf3⟩
  let PostAt (ans : StoreAnswers (List (BitVec 8)) Unit) (evs : List AllocEvent) : SepProp :=
    ⌜(x.model C S parse ans).1 ≠ .error .panic ∧
      kit.callsRel st0 ans (x.model C S parse ans).2 ∧
      ikit.idCallsRel ist0 ans (x.model C S parse ans).2 ∧
      sf.trace = s0.trace ++ ikit.traceOfWith kit encRecord ans (x.model C S parse ans).2 ∧
      WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv parse x evs⌝ ∗
    kit.storeAt x.ssA (kit.storeFinal st0 ans (x.model C S parse ans).2) ∗
    ikit.identityAt x.idA (ikit.idFinal ist0 ans (x.model C S parse ans).2) ∗
    apiEncResultAt A.repAlloc x.ret (x.model C S parse ans).1 ∗
    nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
    protocolAddressAt A.repAlloc x.loc x.locA ∗ tapeAfter ctl x.cur x.rest (x.draws S ans) ∗
    lsLogOff ∗ stackAt s0.sp (withStoresEncStackV kit ikit) ∗
    A.pool lim (M.stepEvents evs st_init) sf
  have hmf4' : sf.mem ⊨ PostAt answers evs_tot ∗ R := hmf4
  have hmf5 : sf.mem ⊨ (∃∗ evs : List AllocEvent, PostAt answers evs) ∗ R :=
    Satisfies.mono (sepConj_mono_left (Entails.sepExists_intro (P := PostAt answers) evs_tot)) hmf4'
  dsimp only [withStoresEncPlacedSpecV, withLsCodeRoLoaded]
  exact Satisfies.mono
    (sepConj_mono_left (Entails.sepExists_intro (P := fun ans => ∃∗ evs, PostAt ans evs) answers))
    hmf5

theorem tailWriteResult_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64} {parse : UuidParser}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (_env : EncEnvPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl parse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit)
    (res : Except (ApiError AddrVal Unit) CiphertextMessage) (w0 w1 w2 w3 : BitVec 64)
    (bs : List (BitVec 8)) (H : SepProp)
    (hm : TailModel kit st0 ikit ist0 C S parse encRecord x answers res s0 s)
    (hst : ResStaged A.repAlloc x.ret res [w0, w1, w2, w3] bs H)
    (hs : EncTailVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
      x st_init st answers (encEntryPlaced + 0x5f8#64)
      (fun sp s => s.readReg64 .x28 = sp + 0x4a0#64 ∧ s.readReg64 .x22 = w0 ∧
        s.readReg64 .x27 = w1 ∧ s.readReg64 .x21 = w2 ∧ s.readReg64 .x23 = w3)
      (fun sp => memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x390 ∗ ((sp + 0x4a0#64) ↦ₛ bs) ∗
        memRegion (sp + 0x578#64) 0x608 ∗ H)
      R s0 s) :
    SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord Hk
      x st_init R s0 s (fun _ => False) :=
  tailWriteResult_placed_ok_core x st_init st R s0 s answers res w0 w1 w2 w3 bs H hm hst hs

end LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailWriteResultPlacedBudget

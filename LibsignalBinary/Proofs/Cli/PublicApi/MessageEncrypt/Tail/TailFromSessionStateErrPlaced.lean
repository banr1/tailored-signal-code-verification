/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailFromSessionStateErr
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.TailDropRecordPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable (`[LibsignalPlacement]`) T1 From-Error (`+0x49c..+0x564`, `tailFromSessionStateErr_placed_ok`)
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.CliRatchet.EncPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open Arm64 ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteResult CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteResult
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailFreePrevSessions CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFreePrevSessions
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecord CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecord

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

set_option maxHeartbeats 800000 in
theorem fromSessionStateErr_placed_sepWP [LibsignalPlacement]
    {Hk : LibsignalHooks}
    {s : State} {sp : BitVec 64}
    {w0 w1 w2 w3 w4 w5 : BitVec 64}
    {u850 u858 u860 u9d0 u9d8 u9e0 uab0 uab8 uac0 uac8 uad0 uad8 : BitVec 64}
    (hpc : s.pc = encEntryPlaced + 0x49c#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp)
    (hx21 : s.readReg64 .x21 = sp + 0x580#64)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64)
    (hx29 : s.readReg64 .x29 = sp + 0xb80#64) :
    SepWP (lsProg_464 Hk)
      (encEntryPlaced + 0x54c#64) s
      (((sp + 0x588#64) ↦₆₄ w0) ∗ ((sp + 0x590#64) ↦₆₄ w1) ∗
        ((sp + 0x598#64) ↦₆₄ w2) ∗ ((sp + 0x5a0#64) ↦₆₄ w3) ∗
        ((sp + 0x5a8#64) ↦₆₄ w4) ∗ ((sp + 0x5b0#64) ↦₆₄ w5) ∗
        ((sp + 0x850#64) ↦₆₄ u850) ∗ ((sp + 0x858#64) ↦₆₄ u858) ∗
        ((sp + 0x860#64) ↦₆₄ u860) ∗
        ((sp + 0x9d0#64) ↦₆₄ u9d0) ∗ ((sp + 0x9d8#64) ↦₆₄ u9d8) ∗
        ((sp + 0x9e0#64) ↦₆₄ u9e0) ∗
        ((sp + 0xab0#64) ↦₆₄ uab0) ∗ ((sp + 0xab8#64) ↦₆₄ uab8) ∗
        ((sp + 0xac0#64) ↦₆₄ uac0) ∗ ((sp + 0xac8#64) ↦₆₄ uac8) ∗
        ((sp + 0xad0#64) ↦₆₄ uad0) ∗ ((sp + 0xad8#64) ↦₆₄ uad8) ∗
        (lsLogFilterAddr ↦₆₄ 0#64))
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.symtab = s.symtab ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = w1 ∧
        sf.readReg64 .x23 = w2 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = w0 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x588#64) ↦₆₄ w0) ∗ ((sp + 0x590#64) ↦₆₄ w1) ∗
          ((sp + 0x598#64) ↦₆₄ w2) ∗ ((sp + 0x5a0#64) ↦₆₄ w3) ∗
          ((sp + 0x5a8#64) ↦₆₄ w4) ∗ ((sp + 0x5b0#64) ↦₆₄ w5) ∗
          ((sp + 0x850#64) ↦₆₄ w3) ∗ ((sp + 0x858#64) ↦₆₄ w4) ∗
          ((sp + 0x860#64) ↦₆₄ w5) ∗
          ((sp + 0x9d0#64) ↦₆₄ w3) ∗ ((sp + 0x9d8#64) ↦₆₄ w4) ∗
          ((sp + 0x9e0#64) ↦₆₄ w5) ∗
          ((sp + 0xab0#64) ↦₆₄ w0) ∗ ((sp + 0xab8#64) ↦₆₄ w1) ∗
          ((sp + 0xac0#64) ↦₆₄ w2) ∗ ((sp + 0xac8#64) ↦₆₄ w3) ∗
          ((sp + 0xad0#64) ↦₆₄ w4) ∗ ((sp + 0xad8#64) ↦₆₄ w5) ∗
          (lsLogFilterAddr ↦₆₄ 0#64))) := by
  subst hsp
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true, lsLogFilterAddr, lsLogFilterSym]
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  exact ⟨rfl, hsp_al, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by sep_ac_rfl⟩

def cliEncCommonRest [LibsignalPlacement] (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (draws : Nat) (s0 : State) : SepProp :=
  (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗
    protocolAddressAt A x.loc x.locA ∗ nowAt s0.sp x.now ∗
    cliTapeAfter ctl x.cur x.rest draws ∗
    stackAt (s0.sp - 0xbe0#64) encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool

theorem encCommonPlaced_eq_logOff_rest [LibsignalPlacement] (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (draws : Nat) (s0 : State) :
    encCommonPlaced A ctl x draws s0 =
      (lsLogFilterAddr ↦₆₄ 0#64) ∗ cliEncCommonRest A ctl x draws s0 := by
  have hlog : FromRecordCallees.lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) := rfl
  unfold encCommonPlaced cliEncCommonRest
  rw [hlog]
  sep_ac_rfl

theorem tailFromSessionStateErr_placed_ok [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    (env : EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord Hk)
    (x : WithStoresEncGhost) (R0 : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8)))
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : EncTailVPlaced kit st0 ikit ist0 C ctl uuidTryParse S x answers
      (encEntryPlaced + 0x49c#64)
      (fun sp s => s.readReg64 .x21 = sp + 0x580#64 ∧ s.readReg64 .x25 = sp + 0x580#64 ∧
        s.readReg64 .x26 = sp + 0x9d0#64 ∧ s.readReg64 .x28 = sp + 0x4a0#64)
      (fun sp => curScratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗ H)
      R0 s0 s) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R0 s0 s (fun _ => False) := by
  let R := encStoreExtraPlaced kit (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
    ikit (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2) x s0 ∗ R0
  rcases hs with ⟨hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hcrl, hvregs⟩,
    ⟨hx21, hx25, hx26, hx28⟩, hstack_le, hmem⟩
  let sp := s0.sp - 0xbe0#64
  change s.mem ⊨
    (curScratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
      memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗ H) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    encCommonPlaced A ctl x (x.draws S answers) s0 ∗ R at hmem
  have h1ea : memRegion (sp + 0x280#64) 0x1ea =
      memRegion (sp + 0x280#64) 0x1e9 ∗ memRegion (sp + 0x469#64) 1 := by
    rw [memRegion_split' (b := sp + 0x280#64) (b' := sp + 0x469#64) (N := 0x1ea) (n := 0x1e9) (k := 1)
          (by decide) (by bv_omega) (by decide)]
  rw [h1ea, encCommonPlaced_eq_logOff_rest A ctl x (x.draws S answers) s0] at hmem
  let F_inv := curScratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
    memRegion (sp + 0x280#64) 0x1e9 ∗ H ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    cliEncCommonRest A ctl x (x.draws S answers) s0 ∗ R
  have hmem_469 : s.mem ⊨
      memRegion (sp + 0x469#64) 1 ∗
      (pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗ F_inv) := by
    have heq :
        ((curScratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
          (memRegion (sp + 0x280#64) 0x1e9 ∗ memRegion (sp + 0x469#64) 1) ∗
          pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         ((lsLogFilterAddr ↦₆₄ 0#64) ∗ cliEncCommonRest A ctl x (x.draws S answers) s0) ∗ R) =
        (memRegion (sp + 0x469#64) 1 ∗
         (pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗
           (lsLogFilterAddr ↦₆₄ 0#64) ∗ F_inv)) := by
      dsimp only [F_inv]; sep_ac_rfl
    rwa [← heq]
  obtain ⟨b469, hmem_b469⟩ := satisfies_memRegion_1 hmem_469
  have hmem_poll : s.mem ⊨
      pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗ (((sp + 0x469#64) ↦₈ b469) ∗ F_inv) := by
    have heq :
        (((sp + 0x469#64) ↦₈ b469) ∗
         (pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗
           (lsLogFilterAddr ↦₆₄ 0#64) ∗ F_inv)) =
        (pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗
         (lsLogFilterAddr ↦₆₄ 0#64) ∗ (((sp + 0x469#64) ↦₈ b469) ∗ F_inv)) := by sep_ac_rfl
    rwa [← heq]
  obtain ⟨u850, u858, u860, u9d0, u9d8, u9e0, uab0, uab8, uac0, uac8, uad0, uad8, hmem_wp⟩ :=
    pollWith_588_mem_elim hmem_poll
  have hx29' : s.readReg64 .x29 = sp + 0xb80#64 := by
    rw [hx29]; dsimp only [sp]; bv_omega
  have hwp := fromSessionStateErr_placed_sepWP (Hk := Hk) (w0 := w0) (w1 := w1) (w2 := w2)
    (w3 := w3) (w4 := w4) (w5 := w5)
    (u850 := u850) (u858 := u858) (u860 := u860) (u9d0 := u9d0) (u9d8 := u9d8) (u9e0 := u9e0)
    (uab0 := uab0) (uab8 := uab8) (uac0 := uac0) (uac8 := uac8) (uad0 := uad0) (uad8 := uad8)
    hpc hrun hsp_al hsp hx21 hx25 hx26 hx28 hx29'
  refine segExit_placed_of_sepWP hmem_wp hwp ?_
  intro s1 P_f hsteps1 hpc1 hrun1 hmf1
    ⟨hsp1, hsp1_al, htr1, _hsym1, hx19_1, hx21_1, hx23_1, _, hx26_1, hx27_1, hx28_1, hx29_1, hvregs1, hPf⟩
  subst hPf
  have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s1 :=
    ⟨hm.1, htr1.trans hm.2⟩
  refine tailDropRecordCur_placed_ok env x R0 s0 s1 answers e w0 w1 w2 w3 w4 w5 H curScratch (Or.inl rfl) g rec b469 hm1 hst ?_
  refine ⟨hpc1, ⟨hrun1, hsp1, hsp0_al, hsp1_al, hx29_1.trans hx29, hx19_1.trans hx19,
    hcrl.of_keepsFrozen hsteps1.keepsFrozen, hvregs1.trans hvregs⟩,
    ⟨hx26_1.trans hx26, hx28_1.trans hx28, hx27_1, hx21_1, hx23_1⟩,
    hstack_le, ?_⟩
  have hmf2 := pollFrom_post_mem_weaken hmf1
  change s1.mem ⊨
    (curScratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
      memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
      pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    encCommonPlaced A ctl x (x.draws S answers) s0 ∗ R
  rw [encCommonPlaced_eq_logOff_rest A ctl x (x.draws S answers) s0]
  have heq :
      (pollWith sp 0x9d0 [w3, w4, w5] ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        (((sp + 0x469#64) ↦₈ b469) ∗ F_inv)) =
      ((curScratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
        memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
        pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
       encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
       ((lsLogFilterAddr ↦₆₄ 0#64) ∗ cliEncCommonRest A ctl x (x.draws S answers) s0) ∗ R) := by
    dsimp only [F_inv]; sep_ac_rfl
  rwa [← heq]

end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr

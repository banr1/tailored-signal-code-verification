/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Segs
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.Common
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.Common
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.TailDropRecordSteps
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.TailFreePrevSessions
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.TailWriteErr
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailDropRecordSteps
import ProofLib.RegChain

@[expose] public section

set_option autoImplicit false

/-!
# Trap-Mode T1 Record-Drop Bridges (`+0x55c` and `+0x54c`)

Proves `tailDropRecordAt55c_ok_trap` and `tailDropRecordCur_ok_trap` for the trap-at-RNG CLI
program.
-/

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession

open CryptoVerification.LibsignalPublicApi.MessageEncrypt

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailFreePrevSessions

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

open CryptoVerification.LibsignalPublicApi.StoreKit

variable {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
  {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
  {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
  {abs : String → Option (State → State)} {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
  {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.tailDropRecordAt55c_ok_trap (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (R0 : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (scratch : BitVec 64 → SepProp)
    (hscr : scratch = curScratch ∨ scratch = cmScratch)
    (prevCap prevPtr : BitVec 64) (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x55c#64) (tailRegs w0 w1 w2)
      (fun sp => scratch sp ∗
        vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        sessionStateAt A (sp + 0x128#64) G st ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H)
      R0 s0 s) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s (fun _ => False) := by
  let R := encStoreExtra kit (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
    ikit (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2) x s0 ∗ R0
  rcases hs with ⟨hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hfl, hsym, hvregs⟩,
    ⟨hx26, hx28, hx27, hx21, hx23⟩, hstack_le, hmem⟩
  rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.entryOf_encEntry_trap (C := C) (abs := abs) env.loads] at hpc
  let sp := s0.sp - 0xbe0#64
  rcases scratch_has_50 hscr sp with ⟨S50, hscr_eq, hscr_weaken⟩
  change s.mem ⊨
    (scratch sp ∗
      vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
      sessionStateAt A (sp + 0x128#64) G st ∗
      memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R at hmem
  rw [hscr_eq] at hmem
  let F := S50 ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
    memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
    nowAt s0.sp x.now ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws S answers) ∗ logOff img ∗
    memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - FromRecordCallees.dropSessionStructureLocal2Stack) ∗
    encSavedRegs s0.sp s0 ∗ R
  have hmem_re : s.mem ⊨
      (((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗ sessionStateAt A (sp + 0x128#64) G st ∗
        A.pool ∗ stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack) ∗ F := by
    have heq :
        (((S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ∗
          vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          sessionStateAt A (sp + 0x128#64) G st ∗
          memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) =
        ((((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗ sessionStateAt A (sp + 0x128#64) G st ∗
          A.pool ∗ stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack) ∗ F) := by
      unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon
      change (((S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ∗
        vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        sessionStateAt A (sp + 0x128#64) G st ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
       encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
       ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        nowAt s0.sp x.now ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws S answers) ∗ logOff img ∗
        stackAt sp encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool) ∗ R) = _
      rw [stackAt_encSubStack_dropSs sp]
      dsimp only [F]
      ac_rfl
    rwa [← heq]
  have hwp := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.dropRecordDropSs_sepWP_trap (G := G) (st := st) env.callees.dropSs hpc hrun hsp_al hsp
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr.segExit_of_sepWP_trap hmem_re hwp ?_
  intro s1 P_f hsteps1 hpc1 hrun1 hmf1
    ⟨hsp1, hsp1_al, htr1, hx19_1, hx21_1, hx23_1, _, hx26_1, hx27_1, hx28_1, hx29_1, hvregs1, hPf⟩
  subst hPf
  have hpc1' : s1.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x564#64 := by
    rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.entryOf_encEntry_trap (C := C) (abs := abs) env.loads, hpc1]
  have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s1 :=
    ⟨hm.1, htr1.trans hm.2⟩
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFreePrevSessions.tailFreePrevSessions_ok_trap env x R0 s0 s1 answers e w0 w1 w2 w3 w4 w5 H prevCap prevPtr hm1 hst ?_
  refine ⟨hpc1', ⟨hrun1, hsp1, hsp0_al, hsp1_al, by reg_chain, by reg_chain,
    hsteps1.frozenLoaded hfl, hsteps1.symtab_eq.trans hsym, hvregs1.trans hvregs⟩, by reg_chain, hstack_le, ?_⟩
  have hmf2 : s1.mem ⊨
      (S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ∗
      (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
       memRegion (sp + 0x128#64) 0x158 ∗
       memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
       encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
       CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by
    have heq :
        ((((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x128#64) 0x158 ∗
          A.pool ∗ stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack) ∗ F) =
        ((S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ∗
         (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          memRegion (sp + 0x128#64) 0x158 ∗
          memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)) := by
      unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon
      change _ = ((S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ∗
        (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
         memRegion (sp + 0x128#64) 0x158 ∗
         memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
          nowAt s0.sp x.now ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws S answers) ∗ logOff img ∗
          stackAt sp encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool) ∗ R))
      rw [stackAt_encSubStack_dropSs sp]
      dsimp only [F]
      ac_rfl
    rwa [← heq]
  have hmf3 := Satisfies.mono (sepConj_mono_left hscr_weaken) hmf2
  have heq2 :
      (memRegion sp 0x58 ∗
       (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        memRegion (sp + 0x128#64) 0x158 ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
        encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)) =
      ((memRegion sp 0x58 ∗
        vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        memRegion (sp + 0x128#64) 0x158 ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
       encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
       CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by ac_rfl
  rwa [← heq2]

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.tailDropRecordCur_ok_trap (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (R0 : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (scratch : BitVec 64 → SepProp)
    (hscr : scratch = curScratch ∨ scratch = cmScratch) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8))) (b469 : BitVec 8)
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x54c#64) (tailRegs w0 w1 w2)
      (fun sp => scratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
        memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
        pollWith sp 0x9d0 [w3, w4, w5] ∗ H)
      R0 s0 s) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s (fun _ => False) := by
  let R := encStoreExtra kit (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
    ikit (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2) x s0 ∗ R0
  rcases hs with ⟨hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hfl, hsym, hvregs⟩,
    ⟨hx26, hx28, hx27, hx21, hx23⟩, hstack_le, hmem⟩
  rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.entryOf_encEntry_trap (C := C) (abs := abs) env.loads] at hpc
  let sp := s0.sp - 0xbe0#64
  change s.mem ⊨
    (scratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
      memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
      pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R at hmem
  unfold sessionRecordAt at hmem
  have h128 : sp + 0x110#64 + 0x18#64 = sp + 0x128#64 := by bv_omega
  have h130 : sp + 0x110#64 + 0x20#64 = sp + 0x130#64 := by bv_omega
  rcases g with ⟨prevCap, prevPtr, _ | G⟩ <;> rcases hcur : rec.currentSession with _ | sess
  · rw [hcur, h128, h130] at hmem
    rcases scratch_has_50 hscr sp with ⟨S50, hscr_eq, hscr_weaken⟩
    have hscr_mem : scratch sp ⊢ memRegion sp 0x58 := hscr_eq ▸ hscr_weaken
    let F := scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
      memRegion (sp + 0x130#64) 336 ∗ memRegion (sp + 0x280#64) 0x1e9 ∗
      pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R
    have hmem_re : s.mem ⊨ (((sp + 0x128#64) ↦₆₄ noneCap) ∗ ((sp + 0x469#64) ↦₈ b469)) ∗ F := by
      have heq :
          ((scratch sp ∗
            (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
              (((sp + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x130#64) 336)) ∗
            memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
            pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) =
          ((((sp + 0x128#64) ↦₆₄ noneCap) ∗ ((sp + 0x469#64) ↦₈ b469)) ∗ F) := by
        dsimp only [F]; ac_rfl
      rwa [← heq]
    have hwp := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.dropRecordCur_none_sepWP_trap (b469 := b469) hpc hrun hsp_al hsp
    refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr.segExit_of_sepWP_trap hmem_re hwp ?_
    intro s1 P_f hsteps1 hpc1 hrun1 hmf1
      ⟨hsp1, hsp1_al, htr1, hsym1, hx19_1, hx21_1, hx23_1, _, hx26_1, hx27_1, hx28_1, hx29_1, hvregs1, hPf⟩
    subst hPf
    have hpc1' : s1.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x564#64 := by
      rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.entryOf_encEntry_trap (C := C) (abs := abs) env.loads, hpc1]
    have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s1 :=
      ⟨hm.1, htr1.trans hm.2⟩
    refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFreePrevSessions.tailFreePrevSessions_ok_trap env x R0 s0 s1 answers e w0 w1 w2 w3 w4 w5 H prevCap prevPtr hm1 hst ?_
    refine ⟨hpc1', ⟨hrun1, hsp1, hsp0_al, hsp1_al, by reg_chain, by reg_chain,
      hsteps1.frozenLoaded hfl, by reg_chain, hvregs1.trans hvregs⟩, by reg_chain, hstack_le, ?_⟩
    have hmf2 : s1.mem ⊨
        (scratch sp ∗
          (((sp + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x130#64) 336) ∗
          (memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ 0#8))) ∗
        (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by
      have heq :
          ((((sp + 0x128#64) ↦₆₄ noneCap) ∗ ((sp + 0x469#64) ↦₈ 0#8)) ∗ F) =
          ((scratch sp ∗
            (((sp + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x130#64) 336) ∗
            (memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ 0#8))) ∗
           (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
             pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)) := by
        dsimp only [F]; ac_rfl
      rwa [← heq]
    have hmf3 := Satisfies.mono
      (sepConj_mono_left (sepConj_mono hscr_mem
        (sepConj_mono (cur_none_weaken sp) (flag_memRegion_weaken sp 0#8)))) hmf2
    have heq2 :
        ((memRegion sp 0x58 ∗ memRegion (sp + 0x128#64) 0x158 ∗ memRegion (sp + 0x280#64) 0x1ea) ∗
         (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
           pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)) =
        ((memRegion sp 0x58 ∗
          vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          memRegion (sp + 0x128#64) 0x158 ∗
          memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by ac_rfl
    rwa [← heq2]
  · rw [hcur] at hmem
    have hfalse : s.mem ⊨ ⌜False⌝ ∗
        (scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by
      have heq :
          ((scratch sp ∗
            (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗ ⌜False⌝) ∗
            memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
            pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) =
          (⌜False⌝ ∗
           (scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
             memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
             pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)) := by ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj] at hfalse
    exact hfalse.1.elim
  · rw [hcur] at hmem
    have hfalse : s.mem ⊨ ⌜False⌝ ∗
        (scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by
      have heq :
          ((scratch sp ∗
            (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗ ⌜False⌝) ∗
            memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
            pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) =
          (⌜False⌝ ∗
           (scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
             memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
             pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)) := by ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj] at hfalse
    exact hfalse.1.elim
  · rw [hcur] at hmem
    dsimp only at hmem
    unfold sessionStateReprAt at hmem
    rw [h128, sessionStateAt_unfold_cap A (sp + 0x128#64) G sess.state] at hmem
    let P_sess_pure : Prop :=
      PendingRel G.pending sess.pendingPreKey ∧ KyberRel G.kyber sess.pendingKyberPreKey ∧
        G.alice.bytes = sess.aliceBaseKey ∧
        G.regIds.take 4 = leBytes 4 sess.remoteRegistrationId.toNat ∧
        (G.regIds.drop 4).take 4 = leBytes 4 sess.localRegistrationId.toNat
    let P_ik_pure : Prop :=
      G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧ G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0
    let F := scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
      ⌜P_ik_pure⌝ ∗ sessionStateAfterLocalIk A (sp + 0x128#64) G sess.state ∗
      memRegion (sp + 0x280#64) 0x1e9 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R
    have hmem_re : s.mem ⊨ ⌜P_sess_pure⌝ ∗ (⌜P_ik_pure⌝ ∗
        ((((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗ ((sp + 0x469#64) ↦₈ b469)) ∗
          (scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
            sessionStateAfterLocalIk A (sp + 0x128#64) G sess.state ∗
            memRegion (sp + 0x280#64) 0x1e9 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
            encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
            CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R))) := by
      have heq :
          ((scratch sp ∗
            (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
              (⌜P_sess_pure⌝ ∗
                (⌜P_ik_pure⌝ ∗
                  (((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗
                    sessionStateAfterLocalIk A (sp + 0x128#64) G sess.state)))) ∗
            memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
            pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) =
          (⌜P_sess_pure⌝ ∗ (⌜P_ik_pure⌝ ∗
            ((((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗ ((sp + 0x469#64) ↦₈ b469)) ∗
              (scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
                sessionStateAfterLocalIk A (sp + 0x128#64) G sess.state ∗
                memRegion (sp + 0x280#64) 0x1e9 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
                encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
                CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)))) := by
        dsimp only [P_sess_pure, P_ik_pure]; ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hmem_re
    rcases hmem_re with ⟨_, h_ik, hmem2⟩
    have hcap_lt : G.localIk.cap.toNat < 2 ^ 63 := h_ik.2.1
    have hwp := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.dropRecordCur_some_sepWP_trap (b469 := b469) hcap_lt hpc hrun hsp_al hsp
    refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr.segExit_of_sepWP_trap hmem2 hwp ?_
    intro s1 P_f hsteps1 hpc1 hrun1 hmf1
      ⟨hsp1, hsp1_al, htr1, hsym1, hx19_1, hx21_1, hx23_1, _, hx26_1, hx27_1, hx28_1, hx29_1, hvregs1, hPf⟩
    subst hPf
    have hpc1' : s1.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x55c#64 := by
      rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.entryOf_encEntry_trap (C := C) (abs := abs) env.loads, hpc1]
    have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s1 :=
      ⟨hm.1, htr1.trans hm.2⟩
    refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.tailDropRecordAt55c_ok_trap env x R0 s0 s1 answers e w0 w1 w2 w3 w4 w5 H scratch hscr
      prevCap prevPtr G sess.state hm1 hst ?_
    refine ⟨hpc1', ⟨hrun1, hsp1, hsp0_al, hsp1_al, by reg_chain, by reg_chain,
      hsteps1.frozenLoaded hfl, by reg_chain, hvregs1.trans hvregs⟩, by reg_chain, hstack_le, ?_⟩
    have hmf1' : s1.mem ⊨ ⌜P_ik_pure⌝ ∗
        ((((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗ ((sp + 0x469#64) ↦₈ 0#8)) ∗
          (scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
            sessionStateAfterLocalIk A (sp + 0x128#64) G sess.state ∗
            memRegion (sp + 0x280#64) 0x1e9 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
            encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
            CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)) := by
      rw [satisfies_pure_sepConj]
      exact ⟨h_ik, hmf1⟩
    have hmf2 : s1.mem ⊨
        (memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ 0#8)) ∗
        (scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          sessionStateAt A (sp + 0x128#64) G sess.state ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by
      have heq :
          (⌜P_ik_pure⌝ ∗
            ((((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗ ((sp + 0x469#64) ↦₈ 0#8)) ∗
              (scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
                sessionStateAfterLocalIk A (sp + 0x128#64) G sess.state ∗
                memRegion (sp + 0x280#64) 0x1e9 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
                encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
                CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R))) =
          ((memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ 0#8)) ∗
           (scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
             sessionStateAt A (sp + 0x128#64) G sess.state ∗
             pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)) := by
        rw [sessionStateAt_unfold_cap A (sp + 0x128#64) G sess.state]
        dsimp only [P_ik_pure]
        ac_rfl
      rwa [← heq]
    have hmf3 := Satisfies.mono (sepConj_mono_left (flag_memRegion_weaken sp 0#8)) hmf2
    have heq2 :
        (memRegion (sp + 0x280#64) 0x1ea ∗
         (scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
           sessionStateAt A (sp + 0x128#64) G sess.state ∗
           pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)) =
        ((scratch sp ∗
          vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          sessionStateAt A (sp + 0x128#64) G sess.state ∗
          memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by ac_rfl
    rwa [← heq2]

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps

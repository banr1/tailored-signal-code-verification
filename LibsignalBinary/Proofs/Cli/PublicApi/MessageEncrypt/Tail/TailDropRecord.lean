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
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailFreePrevSessions

/-!
# T1 Session Record Drop Tail (`+0x46c` and `+0x488`)

Proves `tailDropRecordAfterDealloc_ok` (`+0x488`) and `tailDropRecord_ok` (`+0x46c`), freeing any
live outgoing-ratchet PQ buffer, dropping the current `SessionStructure` if present, and continuing
into `tailFreePrevSessions_ok` at `+0x564`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecord

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

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps

open CryptoVerification.LibsignalPublicApi.StoreKit

set_option maxRecDepth 200000

variable {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
  {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
  {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
  {abs : String → Option (State → State)} {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
  {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecord.tailDropRecordAfterDealloc_ok (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (R0 : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (scratch : BitVec 64 → SepProp)
    (hscr : scratch = curScratch ∨ scratch = cmScratch) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8))) (b469 : BitVec 8)
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x488#64) (tailRegs w0 w1 w2)
      (fun sp => scratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
        memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
        pollWith sp 0x9d0 [w3, w4, w5] ∗ H)
      R0 s0 s) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s (fun _ => False) := by
  let R := encStoreExtra kit (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
    ikit (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2) x s0 ∗ R0
  rcases hs with ⟨hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hfl, hsym, hvregs⟩,
    ⟨hx26, hx28, hx27, hx21, hx23⟩, hstack_le, hmem⟩
  rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.entryOf_encEntry (C := C) (ctl := ctl) (abs := abs) env.loads] at hpc
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
    have hwp := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.dropRecordAfterDealloc_none_sepWP (b469 := b469) hpc hrun hsp_al hsp
    refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr.segExit_of_sepWP hmem_re hwp ?_
    intro s1 P_f hsteps1 hpc1 hrun1 hmf1
      ⟨hsp1, hsp1_al, htr1, hsym1, hx19_1, hx21_1, hx23_1, _, hx26_1, hx27_1, hx28_1, hx29_1, hvregs1, hPf⟩
    subst hPf
    have hpc1' : s1.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x564#64 := by
      rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.entryOf_encEntry (C := C) (ctl := ctl) (abs := abs) env.loads, hpc1]
    have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s1 :=
      ⟨hm.1, htr1.trans hm.2⟩
    refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFreePrevSessions.tailFreePrevSessions_ok env x R0 s0 s1 answers e w0 w1 w2 w3 w4 w5 H prevCap prevPtr hm1 hst ?_
    refine ⟨hpc1', ⟨hrun1, hsp1, hsp0_al, hsp1_al, hx29_1.trans hx29, hx19_1.trans hx19,
      hsteps1.frozenLoaded hfl, hsym1.trans hsym, hvregs1.trans hvregs⟩,
      ⟨hx26_1.trans hx26, hx28_1.trans hx28, hx27_1.trans hx27, hx21_1.trans hx21, hx23_1.trans hx23⟩,
      hstack_le, ?_⟩
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
    have hwp := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.dropRecordAfterDealloc_some_sepWP (b469 := b469) hcap_lt hpc hrun hsp_al hsp
    refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr.segExit_of_sepWP hmem2 hwp ?_
    intro s1 P_f hsteps1 hpc1 hrun1 hmf1
      ⟨hsp1, hsp1_al, htr1, hsym1, hx19_1, hx21_1, hx23_1, _, hx26_1, hx27_1, hx28_1, hx29_1, hvregs1, hPf⟩
    subst hPf
    have hpc1' : s1.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x55c#64 := by
      rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.entryOf_encEntry (C := C) (ctl := ctl) (abs := abs) env.loads, hpc1]
    have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s1 :=
      ⟨hm.1, htr1.trans hm.2⟩
    refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.tailDropRecordAt55c_ok env x R0 s0 s1 answers e w0 w1 w2 w3 w4 w5 H scratch hscr
      prevCap prevPtr G sess.state hm1 hst ?_
    refine ⟨hpc1', ⟨hrun1, hsp1, hsp0_al, hsp1_al, hx29_1.trans hx29, hx19_1.trans hx19,
      hsteps1.frozenLoaded hfl, hsym1.trans hsym, hvregs1.trans hvregs⟩,
      ⟨hx26_1.trans hx26, hx28_1.trans hx28, hx27_1.trans hx27, hx21_1.trans hx21, hx23_1.trans hx23⟩,
      hstack_le, ?_⟩
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

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecord.tailDropRecord_ok (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (R0 : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (scratch : BitVec 64 → SepProp)
    (hscr : scratch = curScratch ∨ scratch = cmScratch) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8)))
    (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8))))
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x46c#64) (tailRegs w0 w1 w2)
      (fun sp => dropRecordSlots A sp scratch g rec ot none (pollWith sp 0x9d0 [w3, w4, w5]) ∗ H)
      R0 s0 s) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s (fun _ => False) := by
  let R := encStoreExtra kit (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
    ikit (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2) x s0 ∗ R0
  rcases hs with ⟨hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hfl, hsym, hvregs⟩,
    ⟨hx26, hx28, hx27, hx21, hx23⟩, hstack_le, hmem⟩
  rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.entryOf_encEntry (C := C) (ctl := ctl) (abs := abs) env.loads] at hpc
  let sp := s0.sp - 0xbe0#64
  change s.mem ⊨
    (dropRecordSlots A sp scratch g rec ot none (pollWith sp 0x9d0 [w3, w4, w5]) ∗ H) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R at hmem
  unfold dropRecordSlots at hmem
  rcases ot with _ | ⟨pqCap, pqPtr, otr⟩
  · have hmem_re : s.mem ⊨ ((sp + 0x469#64) ↦₈ 0#8) ∗
        (scratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
          memRegion (sp + 0x280#64) 0x1e9 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by
      have heq :
          (((scratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗ memRegion (sp + 0x280#64) 8 ∗
            otrSlotAt A sp none ∗ cmSlotAt A sp none ∗ pollWith sp 0x9d0 [w3, w4, w5]) ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) =
          (((sp + 0x469#64) ↦₈ 0#8) ∗
           (scratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
             memRegion (sp + 0x280#64) 0x1e9 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)) := by
        have hslots := otr_none_slots_eq A sp
        have hassoc :
            (scratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗ memRegion (sp + 0x280#64) 8 ∗
              otrSlotAt A sp none ∗ cmSlotAt A sp none ∗ pollWith sp 0x9d0 [w3, w4, w5]) =
            scratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
              (memRegion (sp + 0x280#64) 8 ∗ otrSlotAt A sp none ∗ cmSlotAt A sp none) ∗
              pollWith sp 0x9d0 [w3, w4, w5] := by ac_rfl
        rw [hassoc, hslots]
        ac_rfl
      rwa [← heq]
    have hwp := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.dropRecord_otr_none_sepWP hpc hrun hsp_al hsp
    refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr.segExit_of_sepWP hmem_re hwp ?_
    intro s1 P_f hsteps1 hpc1 hrun1 hmf1
      ⟨hsp1, hsp1_al, htr1, hsym1, hx19_1, hx21_1, hx23_1, _, hx26_1, hx27_1, hx28_1, hx29_1, hvregs1, hPf⟩
    subst hPf
    have hpc1' : s1.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x54c#64 := by
      rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.entryOf_encEntry (C := C) (ctl := ctl) (abs := abs) env.loads, hpc1]
    have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s1 :=
      ⟨hm.1, htr1.trans hm.2⟩
    refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.tailDropRecordCur_ok env x R0 s0 s1 answers e w0 w1 w2 w3 w4 w5 H scratch hscr g rec 0#8 hm1 hst ?_
    refine ⟨hpc1', ⟨hrun1, hsp1, hsp0_al, hsp1_al, hx29_1.trans hx29, hx19_1.trans hx19,
      hsteps1.frozenLoaded hfl, hsym1.trans hsym, hvregs1.trans hvregs⟩,
      ⟨hx26_1.trans hx26, hx28_1.trans hx28, hx27_1.trans hx27, hx21_1.trans hx21, hx23_1.trans hx23⟩,
      hstack_le, ?_⟩
    have heq2 :
        (((sp + 0x469#64) ↦₈ 0#8) ∗
         (scratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
           memRegion (sp + 0x280#64) 0x1e9 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)) =
        ((scratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
          memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by ac_rfl
    rwa [← heq2]
  · unfold otrSlotAt cmSlotAt at hmem
    have h2a0 : sp + 0x288#64 + 0x18#64 = sp + 0x2a0#64 := by bv_omega
    have hotr_w : otrAt A (sp + 0x288#64) pqCap pqPtr otr ⊢
        vecU8At A (sp + 0x288#64) pqCap pqPtr otr.pqrState ∗ memRegion (sp + 0x2a0#64) 176 := by
      have h := otrAt_weaken_vecU8At A (sp + 0x288#64) pqCap pqPtr otr
      rwa [h2a0] at h
    have hmem_otr : s.mem ⊨
        vecU8At A (sp + 0x288#64) pqCap pqPtr otr.pqrState ∗
        (memRegion (sp + 0x2a0#64) 176 ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
          scratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
          memRegion (sp + 0x280#64) 8 ∗ memRegion (sp + 0x350#64) 0x119 ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by
      have hmem_pre : s.mem ⊨
          otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
          (((sp + 0x469#64) ↦₈ 1#8) ∗
            scratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
            memRegion (sp + 0x280#64) 8 ∗ memRegion (sp + 0x350#64) 0x119 ∗
            pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
            encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
            CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by
        have heq :
            (((scratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗ memRegion (sp + 0x280#64) 8 ∗
              (otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗ ((sp + 0x469#64) ↦₈ 1#8)) ∗
              memRegion (sp + 0x350#64) 0x119 ∗ pollWith sp 0x9d0 [w3, w4, w5]) ∗ H) ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) =
            (otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
             (((sp + 0x469#64) ↦₈ 1#8) ∗
               scratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
               memRegion (sp + 0x280#64) 8 ∗ memRegion (sp + 0x350#64) 0x119 ∗
               pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
               encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
               CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)) := by ac_rfl
        rwa [← heq]
      have h1 := Satisfies.mono (sepConj_mono_left hotr_w) hmem_pre
      have heq2 :
          ((vecU8At A (sp + 0x288#64) pqCap pqPtr otr.pqrState ∗ memRegion (sp + 0x2a0#64) 176) ∗
           (((sp + 0x469#64) ↦₈ 1#8) ∗
             scratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
             memRegion (sp + 0x280#64) 8 ∗ memRegion (sp + 0x350#64) 0x119 ∗
             pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)) =
          (vecU8At A (sp + 0x288#64) pqCap pqPtr otr.pqrState ∗
           (memRegion (sp + 0x2a0#64) 176 ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
             scratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
             memRegion (sp + 0x280#64) 8 ∗ memRegion (sp + 0x350#64) 0x119 ∗
             pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)) := by ac_rfl
      rwa [← heq2]
    by_cases hpq : pqCap = 0#64
    · subst hpq
      have h290 : sp + 0x288#64 + 8#64 = sp + 0x290#64 := by bv_omega
      have hvec_w : vecU8At A (sp + 0x288#64) 0#64 pqPtr otr.pqrState ⊢
          ((sp + 0x288#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x290#64) 16 := by
        have h := vecU8At_zero_weaken A (sp + 0x288#64) pqPtr otr.pqrState
        rwa [h290] at h
      have hmem_z := Satisfies.mono (sepConj_mono_left hvec_w) hmem_otr
      let F := memRegion (sp + 0x290#64) 16 ∗ memRegion (sp + 0x2a0#64) 176 ∗
        scratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
        memRegion (sp + 0x280#64) 8 ∗ memRegion (sp + 0x350#64) 0x119 ∗
        pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
        encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R
      have hmem_re : s.mem ⊨ (((sp + 0x288#64) ↦₆₄ 0#64) ∗ ((sp + 0x469#64) ↦₈ 1#8)) ∗ F := by
        have heq :
            ((((sp + 0x288#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x290#64) 16) ∗
             (memRegion (sp + 0x2a0#64) 176 ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
               scratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
               memRegion (sp + 0x280#64) 8 ∗ memRegion (sp + 0x350#64) 0x119 ∗
               pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
               encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
               CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)) =
            ((((sp + 0x288#64) ↦₆₄ 0#64) ∗ ((sp + 0x469#64) ↦₈ 1#8)) ∗ F) := by
          dsimp only [F]; ac_rfl
        rwa [← heq]
      have hwp := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.dropRecord_otr_zero_sepWP hpc hrun hsp_al hsp
      refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr.segExit_of_sepWP hmem_re hwp ?_
      intro s1 P_f hsteps1 hpc1 hrun1 hmf1
        ⟨hsp1, hsp1_al, htr1, hsym1, hx19_1, hx21_1, hx23_1, _, hx26_1, hx27_1, hx28_1, hx29_1, hvregs1, hPf⟩
      subst hPf
      have hpc1' : s1.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x54c#64 := by
        rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.entryOf_encEntry (C := C) (ctl := ctl) (abs := abs) env.loads, hpc1]
      have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s1 :=
        ⟨hm.1, htr1.trans hm.2⟩
      refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.tailDropRecordCur_ok env x R0 s0 s1 answers e w0 w1 w2 w3 w4 w5 H scratch hscr g rec 1#8 hm1 hst ?_
      refine ⟨hpc1', ⟨hrun1, hsp1, hsp0_al, hsp1_al, hx29_1.trans hx29, hx19_1.trans hx19,
        hsteps1.frozenLoaded hfl, hsym1.trans hsym, hvregs1.trans hvregs⟩,
        ⟨hx26_1.trans hx26, hx28_1.trans hx28, hx27_1.trans hx27, hx21_1.trans hx21, hx23_1.trans hx23⟩,
        hstack_le, ?_⟩
      have hmf2 : s1.mem ⊨
          (memRegion (sp + 0x280#64) 8 ∗ ((sp + 0x288#64) ↦₆₄ 0#64) ∗
            memRegion (sp + 0x290#64) 16 ∗ memRegion (sp + 0x2a0#64) 176 ∗
            memRegion (sp + 0x350#64) 0x119) ∗
          (scratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
            ((sp + 0x469#64) ↦₈ 1#8) ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
            encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
            CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by
        have heq :
            ((((sp + 0x288#64) ↦₆₄ 0#64) ∗ ((sp + 0x469#64) ↦₈ 1#8)) ∗ F) =
            ((memRegion (sp + 0x280#64) 8 ∗ ((sp + 0x288#64) ↦₆₄ 0#64) ∗
              memRegion (sp + 0x290#64) 16 ∗ memRegion (sp + 0x2a0#64) 176 ∗
              memRegion (sp + 0x350#64) 0x119) ∗
             (scratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
               ((sp + 0x469#64) ↦₈ 1#8) ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
               encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
               CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)) := by
          dsimp only [F]; ac_rfl
        rwa [← heq]
      have hmf3 := Satisfies.mono (sepConj_mono_left (otr_zero_post_weaken sp)) hmf2
      have heq2 :
          (memRegion (sp + 0x280#64) 0x1e9 ∗
           (scratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
             ((sp + 0x469#64) ↦₈ 1#8) ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)) =
          ((scratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
            memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
            pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by ac_rfl
      rwa [← heq2]
    · have h290 : sp + 0x288#64 + 8#64 = sp + 0x290#64 := by bv_omega
      have h298 : sp + 0x288#64 + 16#64 = sp + 0x298#64 := by bv_omega
      have hvec_w : vecU8At A (sp + 0x288#64) pqCap pqPtr otr.pqrState ⊢
          ((sp + 0x288#64) ↦₆₄ pqCap) ∗ ((sp + 0x290#64) ↦₆₄ pqPtr) ∗
            memRegion (sp + 0x298#64) 8 ∗ A.live pqPtr pqCap.toNat 1 ∗
            memRegion pqPtr pqCap.toNat := by
        have h := vecU8At_nz_weaken A (sp + 0x288#64) pqCap pqPtr otr.pqrState hpq
        rwa [h290, h298] at h
      have hmem_nz := Satisfies.mono (sepConj_mono_left hvec_w) hmem_otr
      let F := memRegion (sp + 0x298#64) 8 ∗ memRegion (sp + 0x2a0#64) 176 ∗
        scratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
        memRegion (sp + 0x280#64) 8 ∗ memRegion (sp + 0x350#64) 0x119 ∗
        pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
        encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
        (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        nowAt s0.sp x.now ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws S answers) ∗ logOff img ∗
        memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - allocHookStack) ∗
        encSavedRegs s0.sp s0 ∗ R
      have hmem_re : s.mem ⊨
          (((sp + 0x288#64) ↦₆₄ pqCap) ∗ ((sp + 0x290#64) ↦₆₄ pqPtr) ∗
            ((sp + 0x469#64) ↦₈ 1#8) ∗ A.pool ∗ A.live pqPtr pqCap.toNat 1 ∗
            memRegion pqPtr pqCap.toNat ∗ stackAt sp allocHookStack) ∗ F := by
        have heq :
            ((((sp + 0x288#64) ↦₆₄ pqCap) ∗ ((sp + 0x290#64) ↦₆₄ pqPtr) ∗
              memRegion (sp + 0x298#64) 8 ∗ A.live pqPtr pqCap.toNat 1 ∗
              memRegion pqPtr pqCap.toNat) ∗
             (memRegion (sp + 0x2a0#64) 176 ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
               scratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
               memRegion (sp + 0x280#64) 8 ∗ memRegion (sp + 0x350#64) 0x119 ∗
               pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
               encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
               CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)) =
            ((((sp + 0x288#64) ↦₆₄ pqCap) ∗ ((sp + 0x290#64) ↦₆₄ pqPtr) ∗
              ((sp + 0x469#64) ↦₈ 1#8) ∗ A.pool ∗ A.live pqPtr pqCap.toNat 1 ∗
              memRegion pqPtr pqCap.toNat ∗ stackAt sp allocHookStack) ∗ F) := by
          unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon
          change ((((sp + 0x288#64) ↦₆₄ pqCap) ∗ ((sp + 0x290#64) ↦₆₄ pqPtr) ∗
            memRegion (sp + 0x298#64) 8 ∗ A.live pqPtr pqCap.toNat 1 ∗
            memRegion pqPtr pqCap.toNat) ∗
           (memRegion (sp + 0x2a0#64) 176 ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
             scratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
             memRegion (sp + 0x280#64) 8 ∗ memRegion (sp + 0x350#64) 0x119 ∗
             pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
              nowAt s0.sp x.now ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws S answers) ∗ logOff img ∗
              stackAt sp encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool) ∗ R)) = _
          rw [stackAt_encSubStack_alloc sp]
          dsimp only [F]
          ac_rfl
        rwa [← heq]
      have hwp := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.dropRecord_otr_nz_sepWP (pqPtr := pqPtr) env.hooks.alloc hpq hpc hrun hsp_al hsp
      refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr.segExit_of_sepWP hmem_re hwp ?_
      intro s1 P_f hsteps1 hpc1 hrun1 hmf1
        ⟨hsp1, hsp1_al, htr1, hx19_1, hx21_1, hx23_1, _, hx26_1, hx27_1, hx28_1, hx29_1, hvregs1, hPf⟩
      subst hPf
      have hpc1' : s1.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x488#64 := by
        rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.entryOf_encEntry (C := C) (ctl := ctl) (abs := abs) env.loads, hpc1]
      have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s1 :=
        ⟨hm.1, htr1.trans hm.2⟩
      refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecord.tailDropRecordAfterDealloc_ok env x R0 s0 s1 answers e w0 w1 w2 w3 w4 w5 H scratch hscr g rec 1#8 hm1 hst ?_
      refine ⟨hpc1', ⟨hrun1, hsp1, hsp0_al, hsp1_al, hx29_1.trans hx29, hx19_1.trans hx19,
        hsteps1.frozenLoaded hfl, hsteps1.symtab_eq.trans hsym, hvregs1.trans hvregs⟩,
        ⟨hx26_1.trans hx26, hx28_1.trans hx28, hx27_1.trans hx27, hx21_1.trans hx21, hx23_1.trans hx23⟩,
        hstack_le, ?_⟩
      have hmf2 : s1.mem ⊨
          (memRegion (sp + 0x280#64) 8 ∗ ((sp + 0x288#64) ↦₆₄ pqCap) ∗
            ((sp + 0x290#64) ↦₆₄ pqPtr) ∗ memRegion (sp + 0x298#64) 8 ∗
            memRegion (sp + 0x2a0#64) 176 ∗ memRegion (sp + 0x350#64) 0x119) ∗
          (scratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
            ((sp + 0x469#64) ↦₈ 1#8) ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
            encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
            CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by
        have heq :
            ((((sp + 0x288#64) ↦₆₄ pqCap) ∗ ((sp + 0x290#64) ↦₆₄ pqPtr) ∗
              ((sp + 0x469#64) ↦₈ 1#8) ∗ A.pool ∗ stackAt sp allocHookStack) ∗ F) =
            ((memRegion (sp + 0x280#64) 8 ∗ ((sp + 0x288#64) ↦₆₄ pqCap) ∗
              ((sp + 0x290#64) ↦₆₄ pqPtr) ∗ memRegion (sp + 0x298#64) 8 ∗
              memRegion (sp + 0x2a0#64) 176 ∗ memRegion (sp + 0x350#64) 0x119) ∗
             (scratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
               ((sp + 0x469#64) ↦₈ 1#8) ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
               encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
               CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)) := by
          unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon
          change _ = ((memRegion (sp + 0x280#64) 8 ∗ ((sp + 0x288#64) ↦₆₄ pqCap) ∗
              ((sp + 0x290#64) ↦₆₄ pqPtr) ∗ memRegion (sp + 0x298#64) 8 ∗
              memRegion (sp + 0x2a0#64) 176 ∗ memRegion (sp + 0x350#64) 0x119) ∗
             (scratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
               ((sp + 0x469#64) ↦₈ 1#8) ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
               encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
               ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
                nowAt s0.sp x.now ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws S answers) ∗ logOff img ∗
                stackAt sp encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool) ∗ R))
          rw [stackAt_encSubStack_alloc sp]
          dsimp only [F]
          ac_rfl
        rwa [← heq]
      have hmf3 := Satisfies.mono (sepConj_mono_left (otr_nz_post_weaken sp pqCap pqPtr)) hmf2
      have heq2 :
          (memRegion (sp + 0x280#64) 0x1e9 ∗
           (scratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
             ((sp + 0x469#64) ↦₈ 1#8) ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)) =
          ((scratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
            memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
            pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by ac_rfl
      rwa [← heq2]

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecord

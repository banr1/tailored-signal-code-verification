/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.Common
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFinishStep
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailDropRecordSteps
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailFreePrevSessions
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailWriteErr
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailWriteResult
import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApiFacts

/-!
# `MessageEncrypt` Finish Segment (`segFinish_ok`)

Verifies `StoredStateV → outcome` (`+0xe88..+0xfac` and result-write tail `+0x5f8..+0x660`): drops
the stored `SessionRecord`, stages the 248-byte `Ok` `CiphertextMessage`, writes `sret`, and returns.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFinish

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteResult
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailFreePrevSessions
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

private theorem encModelOk_priv {C : Crypto} {S : SpqrModel} :
    EncModelOkStmt C S uuidTryParse := by
  rintro x r sess otr taken k m otr' c ⟨hcur, -, hfrom, hrem, hstep5⟩
  unfold EncEncryptStep at hstep5
  cases hp : sess.pendingPreKey with
  | none =>
    rw [hp] at hstep5
    rcases hstep5 with ⟨sm, henc, rfl⟩
    exact ⟨by simp [EncryptGhost.model, messageEncrypt_eq_flat, encryptFlat, wrapFlat, okAnswers,
        storedRecord, hcur, hfrom, hrem, hp, henc],
      by simp [EncryptGhost.draws, EncryptGhost.sendState, loadedSession, okAnswers, hcur, hfrom,
        hrem, hp]⟩
  | some items =>
    rw [hp] at hstep5
    rcases hstep5 with ⟨ts, expiry, sm, hts, hexp, hlt, henc, rfl⟩
    exact ⟨by simp [EncryptGhost.model, messageEncrypt_eq_flat, encryptFlat, wrapFlat, okAnswers,
        storedRecord, hcur, hfrom, hrem, hp, hts, hexp, hlt, henc],
      by simp [EncryptGhost.draws, EncryptGhost.sendState, loadedSession, okAnswers, hcur, hfrom,
        hrem, hp, hts, hexp, hlt, Option.bind]⟩

theorem prev_hdr_378_weaken (sp prevCap prevPtr : BitVec 64) :
    ((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
      ((sp + 0x120#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x128#64) 0x378 ⊢
    memRegion (sp + 0x110#64) 0x390 := by
  have hhdr :
      (((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
        ((sp + 0x120#64) ↦₆₄ 0#64)) =
      words64At (sp + 0x110#64) [prevCap, prevPtr, 0#64] := by
    simp only [words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  have hhdr_mem :
      words64At (sp + 0x110#64) [prevCap, prevPtr, 0#64] ⊢
        memRegion (sp + 0x110#64) 0x18 :=
    words64At_entails_memRegion (sp + 0x110#64) [prevCap, prevPtr, 0#64] (by simp)
  have hjoin :
      memRegion (sp + 0x110#64) 0x390 =
        memRegion (sp + 0x110#64) 0x18 ∗ memRegion (sp + 0x128#64) 0x378 :=
    memRegion_split' (b := sp + 0x110#64) (b' := sp + 0x128#64) (n := 0x18) (k := 0x378)
      (by decide) (by bv_omega) (by decide)
  have hlhs :
      ((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
        ((sp + 0x120#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x128#64) 0x378 =
      words64At (sp + 0x110#64) [prevCap, prevPtr, 0#64] ∗ memRegion (sp + 0x128#64) 0x378 := by
    rw [← hhdr]; ac_rfl
  rw [hlhs, hjoin]
  exact sepConj_mono_left hhdr_mem

theorem mid_280_to_4a0_weaken (sp : BitVec 64) (k : IdentityKey)
    (w0 w1 w2 w3 : BitVec 64) (bws : List (BitVec 64)) (hbws : bws.length = 27) :
    ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      words64At (sp + 0x370#64) [w0, w1, w2, w3] ∗
      words64At (sp + 0x390#64) bws ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
      memRegion (sp + 0x46a#64) 0x36 ⊢
    memRegion (sp + 0x280#64) 0x220 := by
  have h280 := pointsTo64_entails_memRegion (sp + 0x280#64) (sp + 0x128#64)
  have h350 : ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ⊢ memRegion (sp + 0x350#64) 0x20 :=
    Entails.trans (ProofLib.pointsToBytes_entails_memRegion (sp + 0x350#64) k.publicKey.bytes.toList)
      (Entails.of_eq (congrArg (memRegion (sp + 0x350#64)) (List.Vector.toList_length _)))
  have h370 : words64At (sp + 0x370#64) [w0, w1, w2, w3] ⊢ memRegion (sp + 0x370#64) 0x20 :=
    words64At_entails_memRegion (sp + 0x370#64) [w0, w1, w2, w3] (by simp)
  have h390 : words64At (sp + 0x390#64) bws ⊢ memRegion (sp + 0x390#64) 0xd8 := by
    have hlen : (0xd8 : Nat) = 8 * bws.length := by omega
    rw [hlen]
    exact words64At_entails_memRegion (sp + 0x390#64) bws (by omega)
  have h468 : ((sp + 0x468#64) ↦₈ 0#8) ⊢ memRegion (sp + 0x468#64) 1 := by
    rw [memRegion_one]; exact Entails.sepExists_intro 0#8
  have h469 : ((sp + 0x469#64) ↦₈ 0#8) ⊢ memRegion (sp + 0x469#64) 1 := by
    rw [memRegion_one]; exact Entails.sepExists_intro 0#8
  have hjoin :
      memRegion (sp + 0x280#64) 0x220 =
        memRegion (sp + 0x280#64) 8 ∗
          (memRegion (sp + 0x288#64) 200 ∗
            (memRegion (sp + 0x350#64) 0x20 ∗
              (memRegion (sp + 0x370#64) 0x20 ∗
                (memRegion (sp + 0x390#64) 0xd8 ∗
                  (memRegion (sp + 0x468#64) 1 ∗
                    (memRegion (sp + 0x469#64) 1 ∗ memRegion (sp + 0x46a#64) 0x36)))))) := by
    rw [memRegion_split' (b := sp + 0x280#64) (b' := sp + 0x288#64) (n := 8) (k := 0x218)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x288#64) (b' := sp + 0x350#64) (n := 200) (k := 0x150)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x350#64) (b' := sp + 0x370#64) (n := 0x20) (k := 0x130)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x370#64) (b' := sp + 0x390#64) (n := 0x20) (k := 0x110)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x390#64) (b' := sp + 0x468#64) (n := 0xd8) (k := 0x38)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x468#64) (b' := sp + 0x469#64) (n := 1) (k := 0x37)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x469#64) (b' := sp + 0x46a#64) (n := 1) (k := 0x36)
          (by decide) (by bv_omega) (by decide)]
  rw [hjoin]
  exact sepConj_mono h280 (sepConj_mono_right (sepConj_mono h350
    (sepConj_mono h370 (sepConj_mono h390 (sepConj_mono h468 (sepConj_mono_left h469))))))

open CryptoVerification.LibsignalPublicApi.StoreKit

variable {Scope : SessionRecord (List (BitVec 8)) → Prop}
  {Q : List (BitVec 8) → Prop}
  {img : Obj.Image} {C : Crypto} {A : RustAlloc}
  {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
  {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
  {ctl : BitVec 64}
  {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
  {abs : String → Option (State → State)}

theorem segFinish_from_f58 (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (R0 : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (m : CiphertextMessage)
    (w0 w1 w2 w3 : BitVec 64) (bws dws : List (BitVec 64)) (H : SepProp)
    (hbws : bws.length = 27) (hdws : dws.length = 27)
    (hw0_ne : (w0 + 2#64 == 0#64) = false)
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.ok m) s0 s)
    (hst : ResStaged A x.ret (.ok m) [w0, w1, w2, w3] (unpack64List bws) H)
    (hs : EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (encEntry img + 0xf58#64)
      (fun sp s => s.readReg64 .x22 = w0 ∧ s.readReg64 .x26 = sp + 0x9d0#64 ∧
        s.readReg64 .x28 = sp + 0x4a0#64 ∧ s.readReg64 .x27 = w1 ∧
        s.readReg64 .x21 = w2 ∧ s.readReg64 .x23 = w3)
      (fun sp => memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x390 ∗
        words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
        words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H)
      R0 s0 s) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s (fun _ => False) := by
  let R := encStoreExtra kit (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
    ikit (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2) x s0 ∗ R0
  rcases hs with ⟨hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hfl, hsym, hvregs⟩,
    ⟨hx22, hx26, hx28, hx27, hx21, hx23⟩, hstack_le, hmem⟩
  rw [entryOf_encEntry (C := C) (ctl := ctl) (abs := abs) env.loads] at hpc
  let sp := s0.sp - 0xbe0#64
  let F := memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x390 ∗
    memRegion (sp + 0x578#64) 0x458 ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    encCommon A ctl img x (x.draws S answers) s0 ∗ R
  have hmem_re : s.mem ⊨ (words64At (sp + 0x9d0#64) bws ∗ words64At (sp + 0x4a0#64) dws) ∗ F := by
    have heq :
        ((memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x390 ∗
          words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
          words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         encCommon A ctl img x (x.draws S answers) s0 ∗ R) =
        ((words64At (sp + 0x9d0#64) bws ∗ words64At (sp + 0x4a0#64) dws) ∗ F) := by
      dsimp only [F, sp]; ac_rfl
    rwa [← heq]
  have hwp := finish_copyAtF58_sepWP hbws hdws hw0_ne hpc hrun hsp_al hsp hx22 hx26 hx28
  refine segExit_of_sepWP hmem_re hwp ?_
  intro s1 P_f hsteps1 hpc1 hrun1 hmf1
    ⟨hsp1, hsp1_al, htr1, hsym1, hx29_1, hx19_1, hx28_1, hx22_1, hx27_1, hx21_1, hx23_1, hvregs1, hPf⟩
  subst hPf
  have hpc1' : s1.pc = encEntry img + 0x5f8#64 := by
    rw [entryOf_encEntry (C := C) (ctl := ctl) (abs := abs) env.loads, hpc1]
  have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.ok m) s0 s1 :=
    ⟨hm.1, htr1.trans hm.2⟩
  refine tailWriteResult_ok env x R0 s0 s1 answers (.ok m) w0 w1 w2 w3
    (unpack64List bws) H hm1 hst ?_
  refine ⟨hpc1', ⟨hrun1, hsp1, hsp0_al, hsp1_al, hx29_1.trans hx29, hx19_1.trans hx19,
    hsteps1.frozenLoaded hfl, hsym1.trans hsym, hvregs1.trans hvregs⟩,
    ⟨hx28_1, hx22_1, hx27_1.trans hx27, hx21_1.trans hx21, hx23_1.trans hx23⟩,
    hstack_le, ?_⟩
  have hbws_mem : words64At (sp + 0x9d0#64) bws ⊢ memRegion (sp + 0x9d0#64) 0xd8 := by
    have h0xd8 : (0xd8 : Nat) = 8 * bws.length := by omega
    rw [h0xd8]
    exact words64At_entails_memRegion (sp + 0x9d0#64) bws (by omega)
  have hjoin_high :
      memRegion (sp + 0x578#64) 0x608 =
        memRegion (sp + 0x578#64) 0x458 ∗ memRegion (sp + 0x9d0#64) 0xd8 ∗
          memRegion (sp + 0xaa8#64) 0xd8 := by
    rw [memRegion_split' (b := sp + 0x578#64) (b' := sp + 0x9d0#64) (n := 0x458) (k := 0x1b0)
        (by decide) (by bv_omega) (by decide),
      memRegion_split' (b := sp + 0x9d0#64) (b' := sp + 0xaa8#64) (n := 0xd8) (k := 0xd8)
        (by decide) (by bv_omega) (by decide)]
  have hmf2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left hbws_mem)) hmf1
  have heq :
      ((memRegion (sp + 0x9d0#64) 0xd8 ∗ words64At (sp + 0x4a0#64) bws) ∗ F) =
      ((memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x390 ∗
        ((sp + 0x4a0#64) ↦ₛ unpack64List bws) ∗ memRegion (sp + 0x578#64) 0x608 ∗ H) ∗
       encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
       encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by
    dsimp only [F]
    rw [← words64At_eq_pointsToBytes (sp + 0x4a0#64) bws, hjoin_high]
    ac_rfl
  rwa [← heq]

theorem segFinish_from_ef8 (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (R0 : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (m : CiphertextMessage)
    (w0 w1 w2 w3 prevCap prevPtr : BitVec 64) (bws dws : List (BitVec 64)) (H : SepProp)
    (hbws : bws.length = 27) (hdws : dws.length = 27)
    (hw0_ne : (w0 + 2#64 == 0#64) = false)
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.ok m) s0 s)
    (hst : ResStaged A x.ret (.ok m) [w0, w1, w2, w3] (unpack64List bws) H)
    (hs : EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (encEntry img + 0xef8#64)
      (fun sp s => s.readReg64 .x22 = w0 ∧ s.readReg64 .x26 = sp + 0x9d0#64 ∧
        s.readReg64 .x28 = sp + 0x4a0#64 ∧ s.readReg64 .x27 = w1 ∧
        s.readReg64 .x21 = w2 ∧ s.readReg64 .x23 = w3)
      (fun sp => memRegion sp 0x58 ∗
        vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        memRegion (sp + 0x128#64) 0x378 ∗
        words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
        words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H)
      R0 s0 s) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s (fun _ => False) := by
  let R := encStoreExtra kit (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
    ikit (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2) x s0 ∗ R0
  rcases hs with ⟨hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hfl, hsym, hvregs⟩,
    ⟨hx22, hx26, hx28, hx27, hx21, hx23⟩, hstack_le, hmem⟩
  rw [entryOf_encEntry (C := C) (ctl := ctl) (abs := abs) env.loads] at hpc
  let sp := s0.sp - 0xbe0#64
  change s.mem ⊨
    (memRegion sp 0x58 ∗
      vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
      memRegion (sp + 0x128#64) 0x378 ∗
      words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
      words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    encCommon A ctl img x (x.draws S answers) s0 ∗ R at hmem
  by_cases hcap : prevCap = 0#64
  · subst hcap
    rw [vecAt_prev_zero_eq A sp prevPtr] at hmem
    let F := memRegion sp 0x58 ∗ memRegion (sp + 0x128#64) 0x378 ∗
      words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
      words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
      encCommon A ctl img x (x.draws S answers) s0 ∗ R
    have hmem_re : s.mem ⊨
        ⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
        ((((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64)) ∗ F) := by
      have heq :
          ((memRegion sp 0x58 ∗
            (⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
              (((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64))) ∗
            memRegion (sp + 0x128#64) 0x378 ∗
            words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
            words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommon A ctl img x (x.draws S answers) s0 ∗ R) =
          (⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
           ((((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64)) ∗ F)) := by
        dsimp only [F]; ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj] at hmem_re
    have hwp := finish_prev_zero_sepWP (prevPtr := prevPtr) hpc hrun hsp_al hsp
    refine segExit_of_sepWP hmem_re.2 hwp ?_
    intro s1 P_f hsteps1 hpc1 hrun1 hmf1
      ⟨hsp1, hsp1_al, htr1, hsym1, hx19_1, hx21_1, hx22_1, hx23_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs1, hPf⟩
    subst hPf
    have hpc1' : s1.pc = encEntry img + 0xf58#64 := by
      rw [entryOf_encEntry (C := C) (ctl := ctl) (abs := abs) env.loads, hpc1]
    have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.ok m) s0 s1 :=
      ⟨hm.1, htr1.trans hm.2⟩
    refine segFinish_from_f58 env x R0 s0 s1 answers m
      w0 w1 w2 w3 bws dws H hbws hdws hw0_ne hm1 hst ?_
    refine ⟨hpc1', ⟨hrun1, hsp1, hsp0_al, hsp1_al, hx29_1.trans hx29, hx19_1.trans hx19,
      hsteps1.frozenLoaded hfl, hsym1.trans hsym, hvregs1.trans hvregs⟩,
      ⟨hx22_1.trans hx22, hx26_1.trans hx26, hx28_1.trans hx28,
       hx27_1.trans hx27, hx21_1.trans hx21, hx23_1.trans hx23⟩,
      hstack_le, ?_⟩
    have hmf2 : s1.mem ⊨
        (((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
          ((sp + 0x120#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x128#64) 0x378) ∗
        (memRegion sp 0x58 ∗ words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
          words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by
      have heq :
          ((((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64)) ∗ F) =
          ((((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
            ((sp + 0x120#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x128#64) 0x378) ∗
          (memRegion sp 0x58 ∗ words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
            words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
            encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
            encCommon A ctl img x (x.draws S answers) s0 ∗ R)) := by
        dsimp only [F]; ac_rfl
      rwa [← heq]
    have hmf3 := Satisfies.mono (sepConj_mono_left (prev_hdr_378_weaken sp 0#64 prevPtr)) hmf2
    have heq2 :
        (memRegion (sp + 0x110#64) 0x390 ∗
         (memRegion sp 0x58 ∗ words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
          words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommon A ctl img x (x.draws S answers) s0 ∗ R)) =
        ((memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x390 ∗
          words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
          words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by ac_rfl
    rwa [← heq2]
  · rw [vecAt_prev_nz_eq A sp prevCap prevPtr hcap] at hmem
    let F := memRegion sp 0x58 ∗ memRegion (sp + 0x128#64) 0x378 ∗
      words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
      words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
      (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
      nowAt s0.sp x.now ∗ tapeAfter ctl x.cur x.rest (x.draws S answers) ∗ logOff img ∗
      memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - allocHookStack) ∗
      encSavedRegs s0.sp s0 ∗ R
    have hmem_re : s.mem ⊨
        ⌜0 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
        ((((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64) ∗
          A.pool ∗ A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24) ∗
          stackAt sp allocHookStack) ∗ F) := by
      have heq :
          ((memRegion sp 0x58 ∗
            (⌜0 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
              (((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64) ∗
               A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24))) ∗
            memRegion (sp + 0x128#64) 0x378 ∗
            words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
            words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommon A ctl img x (x.draws S answers) s0 ∗ R) =
          (⌜0 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
           ((((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64) ∗
             A.pool ∗ A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24) ∗
             stackAt sp allocHookStack) ∗ F)) := by
        unfold encCommon
        change ((memRegion sp 0x58 ∗
          (⌜0 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
            (((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64) ∗
             A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24))) ∗
          memRegion (sp + 0x128#64) 0x378 ∗
          words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
          words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
          nowAt s0.sp x.now ∗ tapeAfter ctl x.cur x.rest (x.draws S answers) ∗ logOff img ∗
          stackAt sp encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool) ∗ R) = _
        rw [stackAt_encSubStack_alloc sp]
        dsimp only [F]
        ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj] at hmem_re
    rcases hmem_re with ⟨⟨_, hcap_lt, _⟩, hmem2⟩
    have hwp := finish_prev_nz_sepWP (prevPtr := prevPtr) env.hooks.alloc hcap hcap_lt hpc hrun hsp_al hsp
    refine segExit_of_sepWP hmem2 hwp ?_
    intro s1 P_f hsteps1 hpc1 hrun1 hmf1
      ⟨hsp1, hsp1_al, htr1, hx19_1, hx21_1, hx22_1, hx23_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs1, hPf⟩
    subst hPf
    have hpc1' : s1.pc = encEntry img + 0xf58#64 := by
      rw [entryOf_encEntry (C := C) (ctl := ctl) (abs := abs) env.loads, hpc1]
    have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.ok m) s0 s1 :=
      ⟨hm.1, htr1.trans hm.2⟩
    refine segFinish_from_f58 env x R0 s0 s1 answers m
      w0 w1 w2 w3 bws dws H hbws hdws hw0_ne hm1 hst ?_
    refine ⟨hpc1', ⟨hrun1, hsp1, hsp0_al, hsp1_al, hx29_1.trans hx29, hx19_1.trans hx19,
      hsteps1.frozenLoaded hfl, hsteps1.symtab_eq.trans hsym, hvregs1.trans hvregs⟩,
      ⟨hx22_1.trans hx22, hx26_1.trans hx26, hx28_1.trans hx28,
       hx27_1.trans hx27, hx21_1.trans hx21, hx23_1.trans hx23⟩,
      hstack_le, ?_⟩
    have hmf2 : s1.mem ⊨
        (((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
          ((sp + 0x120#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x128#64) 0x378) ∗
        (memRegion sp 0x58 ∗ words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
          words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by
      have heq :
          ((((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
            ((sp + 0x120#64) ↦₆₄ 0#64) ∗ A.pool ∗ stackAt sp allocHookStack) ∗ F) =
          ((((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
            ((sp + 0x120#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x128#64) 0x378) ∗
           (memRegion sp 0x58 ∗ words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
            words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
            encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
            encCommon A ctl img x (x.draws S answers) s0 ∗ R)) := by
        unfold encCommon
        change _ = ((((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
          ((sp + 0x120#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x128#64) 0x378) ∗
         (memRegion sp 0x58 ∗ words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
          words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
           nowAt s0.sp x.now ∗ tapeAfter ctl x.cur x.rest (x.draws S answers) ∗ logOff img ∗
           stackAt sp encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool) ∗ R))
        rw [stackAt_encSubStack_alloc sp]
        dsimp only [F]
        ac_rfl
      rwa [← heq]
    have hmf3 := Satisfies.mono (sepConj_mono_left (prev_hdr_378_weaken sp prevCap prevPtr)) hmf2
    have heq2 :
        (memRegion (sp + 0x110#64) 0x390 ∗
         (memRegion sp 0x58 ∗ words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
          words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommon A ctl img x (x.draws S answers) s0 ∗ R)) =
        ((memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x390 ∗
          words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
          words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by ac_rfl
    rwa [← heq2]

theorem segFinish_from_ef0 (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (R0 : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (m : CiphertextMessage)
    (w0 w1 w2 w3 prevCap prevPtr : BitVec 64) (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (bws dws : List (BitVec 64)) (H : SepProp)
    (hbws : bws.length = 27) (hdws : dws.length = 27)
    (hw0_ne : (w0 + 2#64 == 0#64) = false)
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.ok m) s0 s)
    (hst : ResStaged A x.ret (.ok m) [w0, w1, w2, w3] (unpack64List bws) H)
    (hs : EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (encEntry img + 0xef0#64)
      (fun sp s => s.readReg64 .x22 = w0 ∧ s.readReg64 .x26 = sp + 0x9d0#64 ∧
        s.readReg64 .x28 = sp + 0x4a0#64 ∧ s.readReg64 .x27 = w1 ∧
        s.readReg64 .x21 = w2 ∧ s.readReg64 .x23 = w3)
      (fun sp => cmScratch sp ∗
        vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        sessionStateAt A (sp + 0x128#64) G st ∗
        memRegion (sp + 0x280#64) 0x220 ∗
        words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
        words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H)
      R0 s0 s) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s (fun _ => False) := by
  let R := encStoreExtra kit (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
    ikit (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2) x s0 ∗ R0
  rcases hs with ⟨hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hfl, hsym, hvregs⟩,
    ⟨hx22, hx26, hx28, hx27, hx21, hx23⟩, hstack_le, hmem⟩
  rw [entryOf_encEntry (C := C) (ctl := ctl) (abs := abs) env.loads] at hpc
  let sp := s0.sp - 0xbe0#64
  rcases scratch_has_50 (Or.inr rfl) sp with ⟨S50, hscr_eq, hscr_weaken⟩
  change s.mem ⊨
    (cmScratch sp ∗
      vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
      sessionStateAt A (sp + 0x128#64) G st ∗
      memRegion (sp + 0x280#64) 0x220 ∗
      words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
      words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    encCommon A ctl img x (x.draws S answers) s0 ∗ R at hmem
  rw [hscr_eq] at hmem
  let F := S50 ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
    memRegion (sp + 0x280#64) 0x220 ∗
    words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
    words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
    nowAt s0.sp x.now ∗ tapeAfter ctl x.cur x.rest (x.draws S answers) ∗ logOff img ∗
    memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - FromRecordCallees.dropSessionStructureLocal2Stack) ∗
    encSavedRegs s0.sp s0 ∗ R
  have hmem_re : s.mem ⊨
      (((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗ sessionStateAt A (sp + 0x128#64) G st ∗
        A.pool ∗ stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack) ∗ F := by
    have heq :
        (((S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ∗
          vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          sessionStateAt A (sp + 0x128#64) G st ∗
          memRegion (sp + 0x280#64) 0x220 ∗
          words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
          words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         encCommon A ctl img x (x.draws S answers) s0 ∗ R) =
        ((((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗ sessionStateAt A (sp + 0x128#64) G st ∗
          A.pool ∗ stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack) ∗ F) := by
      unfold encCommon
      change (((S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ∗
        vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        sessionStateAt A (sp + 0x128#64) G st ∗
        memRegion (sp + 0x280#64) 0x220 ∗
        words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
        words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H) ∗
       encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
       ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        nowAt s0.sp x.now ∗ tapeAfter ctl x.cur x.rest (x.draws S answers) ∗ logOff img ∗
        stackAt sp encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool) ∗ R) = _
      rw [stackAt_encSubStack_dropSs sp]
      dsimp only [F]
      ac_rfl
    rwa [← heq]
  have hwp := finish_dropSs_sepWP (G := G) (st := st) env.callees.dropSs hpc hrun hsp_al hsp
  refine segExit_of_sepWP hmem_re hwp ?_
  intro s1 P_f hsteps1 hpc1 hrun1 hmf1
    ⟨hsp1, hsp1_al, htr1, hx19_1, hx21_1, hx22_1, hx23_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs1, hPf⟩
  subst hPf
  have hpc1' : s1.pc = encEntry img + 0xef8#64 := by
    rw [entryOf_encEntry (C := C) (ctl := ctl) (abs := abs) env.loads, hpc1]
  have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.ok m) s0 s1 :=
    ⟨hm.1, htr1.trans hm.2⟩
  refine segFinish_from_ef8 env x R0 s0 s1 answers m
    w0 w1 w2 w3 prevCap prevPtr bws dws H
    hbws hdws hw0_ne hm1 hst ?_
  refine ⟨hpc1', ⟨hrun1, hsp1, hsp0_al, hsp1_al, hx29_1.trans hx29, hx19_1.trans hx19,
    hsteps1.frozenLoaded hfl, hsteps1.symtab_eq.trans hsym, hvregs1.trans hvregs⟩,
    ⟨hx22_1.trans hx22, hx26_1.trans hx26, hx28_1.trans hx28,
     hx27_1.trans hx27, hx21_1.trans hx21, hx23_1.trans hx23⟩,
    hstack_le, ?_⟩
  have hjoin_128 :
      memRegion (sp + 0x128#64) 0x158 ∗ memRegion (sp + 0x280#64) 0x220 =
        memRegion (sp + 0x128#64) 0x378 :=
    (memRegion_split' (b := sp + 0x128#64) (b' := sp + 0x280#64) (n := 0x158) (k := 0x220)
      (by decide) (by bv_omega) (by decide)).symm
  have hmf2 : s1.mem ⊨
      (S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ∗
      (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
       memRegion (sp + 0x128#64) 0x378 ∗
       words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
       words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
       encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
       encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by
    have heq :
        ((((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x128#64) 0x158 ∗
          A.pool ∗ stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack) ∗ F) =
        ((S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ∗
         (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          memRegion (sp + 0x128#64) 0x378 ∗
          words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
          words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommon A ctl img x (x.draws S answers) s0 ∗ R)) := by
      unfold encCommon
      change _ = ((S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ∗
        (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
         memRegion (sp + 0x128#64) 0x378 ∗
         words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
         words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
          nowAt s0.sp x.now ∗ tapeAfter ctl x.cur x.rest (x.draws S answers) ∗ logOff img ∗
          stackAt sp encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool) ∗ R))
      rw [stackAt_encSubStack_dropSs sp, ← hjoin_128]
      dsimp only [F]
      ac_rfl
    rwa [← heq]
  have hmf3 := Satisfies.mono (sepConj_mono_left hscr_weaken) hmf2
  have heq2 :
      (memRegion sp 0x58 ∗
       (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        memRegion (sp + 0x128#64) 0x378 ∗
        words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
        words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
        encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
        encCommon A ctl img x (x.draws S answers) s0 ∗ R)) =
      ((memRegion sp 0x58 ∗
        vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        memRegion (sp + 0x128#64) 0x378 ∗
        words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
        words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H) ∗
       encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
       encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by ac_rfl
  rwa [← heq2]

theorem segFinish_okV : SegFinishSpecV kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs := by
  intro env x r sess otr taken k m otr' c R0 s0 s hstored
  rcases hstored with ⟨⟨h1to5, htrustRel, hsaveRel, hstoreRel⟩, hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hfl, hsym, hvregs⟩,
    htrace, ⟨hx26, hx28⟩, _, _, _, _, hstack_le, hmem⟩
  have ⟨hmod_eq, hdraws_eq⟩ := encModelOk_priv x r sess otr taken k m otr' c (h1to5.inScope env.scopeIn)
  have hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x (okAnswers r c) (.ok m) s0 s := by
    refine ⟨⟨by rw [hmod_eq], ?_, ?_⟩, ?_⟩
    · rw [hmod_eq]
      exact ⟨h1to5.2.1.2, hstoreRel, trivial⟩
    · rw [hmod_eq]
      exact ⟨htrustRel, hsaveRel, trivial⟩
    · rw [htrace, hmod_eq]
      dsimp only
      rw [ikit.traceOfWith_all4 kit]
      simp only [okAnswers, List.append_assoc]
  have hstf : kit.storeFinal st0 (okAnswers r c) (x.model C S uuidTryParse (okAnswers r c)).2 =
      kit.storeUpdate st0 x.rem.val (storedRecord sess otr' taken) (.ok ()) := by
    rw [hmod_eq]
    rfl
  have hidf : ikit.idFinal ist0 (okAnswers r c) (x.model C S uuidTryParse (okAnswers r c)).2 =
      ikit.saveUpdate (ikit.trustUpdate ist0 x.rem.val k .sending (.ok true)) x.rem.val k (.ok c) := by
    rw [hmod_eq]
    rfl
  rw [← hdraws_eq, ← hstf, ← hidf] at hmem
  let R := encStoreExtra kit (kit.storeFinal st0 (okAnswers r c) (x.model C S uuidTryParse (okAnswers r c)).2)
    ikit (ikit.idFinal ist0 (okAnswers r c) (x.model C S uuidTryParse (okAnswers r c)).2) x s0 ∗ R0
  let sp := s0.sp - 0xbe0#64
  change s.mem ⊨
    ((∃∗ g : RecordGhost,
        sessionRecordAt A (sp + 0x110#64) g (storedRecord sess otr' taken)) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ apiEncResultAt A (sp + 0x370#64) (.ok m) ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ memRegion (sp + 0x469#64) 1) ∗
    cmScratch sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
    memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
    encCommon A ctl img x (x.draws S (okAnswers r c)) s0 ∗ R at hmem
  have hmem_g : s.mem ⊨
      (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x110#64) g (storedRecord sess otr' taken)) ∗
      (apiEncResultAt A (sp + 0x370#64) (.ok m) ∗ memRegion (sp + 0x469#64) 1 ∗
       memRegion (sp + 0x46a#64) 0x716 ∗
       (cmScratch sp ∗ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
        encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
        encCommon A ctl img x (x.draws S (okAnswers r c)) s0 ∗ R)) := by
    have heq :
        (((∃∗ g : RecordGhost,
            sessionRecordAt A (sp + 0x110#64) g (storedRecord sess otr' taken)) ∗
          ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
          ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ apiEncResultAt A (sp + 0x370#64) (.ok m) ∗
          ((sp + 0x468#64) ↦₈ 0#8) ∗ memRegion (sp + 0x469#64) 1) ∗
         cmScratch sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
         memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
         encCommon A ctl img x (x.draws S (okAnswers r c)) s0 ∗ R) =
        ((∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x110#64) g (storedRecord sess otr' taken)) ∗
         (apiEncResultAt A (sp + 0x370#64) (.ok m) ∗ memRegion (sp + 0x469#64) 1 ∗
          memRegion (sp + 0x46a#64) 0x716 ∗
          (cmScratch sp ∗ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
           ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommon A ctl img x (x.draws S (okAnswers r c)) s0 ∗ R))) := by ac_rfl
    rwa [← heq]
  rw [sepExists_sepConj_left, satisfies_sepExists] at hmem_g
  obtain ⟨⟨prevCap, prevPtr, _ | G⟩, hmem_g⟩ := hmem_g
  · unfold sessionRecordAt storedRecord at hmem_g
    rw [sepConj_assoc, sepConj_comm (vecAt _ _ _ _ _ _ _ _), sepConj_assoc,
      satisfies_pure_sepConj] at hmem_g
    exact hmem_g.1.elim
  unfold sessionRecordAt storedRecord sessionStateReprAt at hmem_g
  have h128 : sp + 0x110#64 + 0x18#64 = sp + 0x128#64 := by bv_omega
  rw [h128] at hmem_g
  dsimp only at hmem_g
  rw [sessionStateAt_unfold_cap] at hmem_g
  have hmem_cm : s.mem ⊨ apiEncResultAt A (sp + 0x370#64) (.ok m) ∗
      (⌜PendingRel G.pending sess.pendingPreKey ∧ KyberRel G.kyber sess.pendingKyberPreKey ∧
        G.alice.bytes = sess.aliceBaseKey ∧ G.regIds.take 4 = leBytes 4 sess.remoteRegistrationId.toNat ∧
        (G.regIds.drop 4).take 4 = leBytes 4 sess.localRegistrationId.toNat⌝ ∗
       ⌜G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧ G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0⌝ ∗
       ((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗
       sessionStateAfterLocalIk A (sp + 0x128#64) G (otr'.applyToSessionState taken) ∗
       vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
       memRegion (sp + 0x469#64) 1 ∗ memRegion (sp + 0x46a#64) 0x716 ∗
       cmScratch sp ∗ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
       ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
       encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
       encCommon A ctl img x (x.draws S (okAnswers r c)) s0 ∗ R) := by
    have heq :
        ((vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          (⌜PendingRel G.pending sess.pendingPreKey ∧ KyberRel G.kyber sess.pendingKyberPreKey ∧
            G.alice.bytes = sess.aliceBaseKey ∧ G.regIds.take 4 = leBytes 4 sess.remoteRegistrationId.toNat ∧
            (G.regIds.drop 4).take 4 = leBytes 4 sess.localRegistrationId.toNat⌝ ∗
           (⌜G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧ G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0⌝ ∗
            (((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗
             sessionStateAfterLocalIk A (sp + 0x128#64) G (otr'.applyToSessionState taken))))) ∗
         (apiEncResultAt A (sp + 0x370#64) (.ok m) ∗ memRegion (sp + 0x469#64) 1 ∗
          memRegion (sp + 0x46a#64) 0x716 ∗
          (cmScratch sp ∗ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
           ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommon A ctl img x (x.draws S (okAnswers r c)) s0 ∗ R))) =
        (apiEncResultAt A (sp + 0x370#64) (.ok m) ∗
         (⌜PendingRel G.pending sess.pendingPreKey ∧ KyberRel G.kyber sess.pendingKyberPreKey ∧
           G.alice.bytes = sess.aliceBaseKey ∧ G.regIds.take 4 = leBytes 4 sess.remoteRegistrationId.toNat ∧
           (G.regIds.drop 4).take 4 = leBytes 4 sess.localRegistrationId.toNat⌝ ∗
          ⌜G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧ G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0⌝ ∗
          ((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗
          sessionStateAfterLocalIk A (sp + 0x128#64) G (otr'.applyToSessionState taken) ∗
          vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          memRegion (sp + 0x469#64) 1 ∗ memRegion (sp + 0x46a#64) 0x716 ∗
          cmScratch sp ∗ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
          ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommon A ctl img x (x.draws S (okAnswers r c)) s0 ∗ R)) := by ac_rfl
    rwa [← heq]
  obtain ⟨w0, w1, w2, w3, bws, H, hbws, hw0_ne, hst, hmem_words⟩ :=
    extract_ok_cm (ret := x.ret) hmem_cm
  have h390 : sp + 0x370#64 + 0x20#64 = sp + 0x390#64 := by bv_omega
  rw [h390] at hmem_words
  have hpoll_split :
      memRegion (sp + 0x46a#64) 0x716 =
        memRegion (sp + 0x46a#64) 0x36 ∗ memRegion (sp + 0x4a0#64) (8 * 27) ∗
          memRegion (sp + 0x578#64) 0x458 ∗ memRegion (sp + 0x9d0#64) (8 * 27) ∗
          memRegion (sp + 0xaa8#64) 0xd8 := by
    rw [memRegion_split' (b := sp + 0x46a#64) (b' := sp + 0x4a0#64) (n := 0x36) (k := 0x6e0)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x4a0#64) (b' := sp + 0x578#64) (n := 8 * 27) (k := 0x608)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x578#64) (b' := sp + 0x9d0#64) (n := 0x458) (k := 0x1b0)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x9d0#64) (b' := sp + 0xaa8#64) (n := 8 * 27) (k := 0xd8)
          (by decide) (by bv_omega) (by decide)]
  rw [hpoll_split, memRegion_one (sp + 0x469#64)] at hmem_words
  let F0 := ((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗
    words64At (sp + 0x370#64) [w0, w1, w2, w3] ∗ words64At (sp + 0x390#64) bws ∗ H ∗
    sessionStateAfterLocalIk A (sp + 0x128#64) G (otr'.applyToSessionState taken) ∗
    vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
    memRegion (sp + 0x46a#64) 0x36 ∗ memRegion (sp + 0x578#64) 0x458 ∗
    memRegion (sp + 0xaa8#64) 0xd8 ∗
    cmScratch sp ∗ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
    ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    encCommon A ctl img x (x.draws S (okAnswers r c)) s0 ∗ R
  have hmem_p : s.mem ⊨
      ⌜G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧ G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0⌝ ∗
      ((∃∗ b469 : BitVec 8, (sp + 0x469#64) ↦₈ b469) ∗
       (memRegion (sp + 0x4a0#64) (8 * 27) ∗ (memRegion (sp + 0x9d0#64) (8 * 27) ∗ F0))) := by
    have heq :
        (words64At (sp + 0x370#64) [w0, w1, w2, w3] ∗ words64At (sp + 0x390#64) bws ∗ H ∗
         (⌜PendingRel G.pending sess.pendingPreKey ∧ KyberRel G.kyber sess.pendingKyberPreKey ∧
           G.alice.bytes = sess.aliceBaseKey ∧ G.regIds.take 4 = leBytes 4 sess.remoteRegistrationId.toNat ∧
           (G.regIds.drop 4).take 4 = leBytes 4 sess.localRegistrationId.toNat⌝ ∗
          ⌜G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧ G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0⌝ ∗
          ((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗
          sessionStateAfterLocalIk A (sp + 0x128#64) G (otr'.applyToSessionState taken) ∗
          vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          (∃∗ b469 : BitVec 8, (sp + 0x469#64) ↦₈ b469) ∗
          (memRegion (sp + 0x46a#64) 0x36 ∗ (memRegion (sp + 0x4a0#64) (8 * 27) ∗
           (memRegion (sp + 0x578#64) 0x458 ∗ (memRegion (sp + 0x9d0#64) (8 * 27) ∗
            memRegion (sp + 0xaa8#64) 0xd8)))) ∗
          cmScratch sp ∗ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
          ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommon A ctl img x (x.draws S (okAnswers r c)) s0 ∗ R)) =
        (⌜PendingRel G.pending sess.pendingPreKey ∧ KyberRel G.kyber sess.pendingKyberPreKey ∧
           G.alice.bytes = sess.aliceBaseKey ∧ G.regIds.take 4 = leBytes 4 sess.remoteRegistrationId.toNat ∧
           (G.regIds.drop 4).take 4 = leBytes 4 sess.localRegistrationId.toNat⌝ ∗
         (⌜G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧ G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0⌝ ∗
          ((∃∗ b469 : BitVec 8, (sp + 0x469#64) ↦₈ b469) ∗
           (memRegion (sp + 0x4a0#64) (8 * 27) ∗ (memRegion (sp + 0x9d0#64) (8 * 27) ∗ F0))))) := by
      dsimp only [F0]; ac_rfl
    rw [heq, satisfies_pure_sepConj] at hmem_words
    exact hmem_words.2
  rw [satisfies_pure_sepConj] at hmem_p
  rcases hmem_p with ⟨⟨hcap_le, hcap_lt, hptr_nz⟩, hmem_p⟩
  rw [sepExists_sepConj_left, satisfies_sepExists] at hmem_p
  obtain ⟨b469, hmem_p⟩ := hmem_p
  rw [sepConj_comm ((sp + 0x469#64) ↦₈ b469), sepConj_assoc] at hmem_p
  obtain ⟨dws, hdws, hmem_d⟩ :=
    memRegion_eq_exists_words64At 27 (sp + 0x4a0#64) (by decide) s.mem _ hmem_p
  rw [sepConj_comm (words64At (sp + 0x4a0#64) dws), sepConj_assoc, sepConj_assoc] at hmem_d
  obtain ⟨dws9d0, hdws9d0, hmem_d2⟩ :=
    memRegion_eq_exists_words64At 27 (sp + 0x9d0#64) (by decide) s.mem _ hmem_d
  let F1 := words64At (sp + 0x4a0#64) dws ∗ H ∗
    sessionStateAfterLocalIk A (sp + 0x128#64) G (otr'.applyToSessionState taken) ∗
    vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
    memRegion (sp + 0x46a#64) 0x36 ∗ memRegion (sp + 0x578#64) 0x458 ∗
    memRegion (sp + 0xaa8#64) 0xd8 ∗
    cmScratch sp ∗ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
    ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    encCommon A ctl img x (x.draws S (okAnswers r c)) s0 ∗ R
  have hmem_stage : s.mem ⊨
      (((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗
        words64At (sp + 0x370#64) [w0, w1, w2, w3] ∗
        words64At (sp + 0x390#64) bws ∗
        ((sp + 0x469#64) ↦₈ b469) ∗
        words64At (sp + 0x9d0#64) dws9d0) ∗ F1 := by
    have heq :
        (words64At (sp + 0x9d0#64) dws9d0 ∗
         (F0 ∗ (((sp + 0x469#64) ↦₈ b469) ∗ words64At (sp + 0x4a0#64) dws))) =
        ((((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗
          words64At (sp + 0x370#64) [w0, w1, w2, w3] ∗
          words64At (sp + 0x390#64) bws ∗
          ((sp + 0x469#64) ↦₈ b469) ∗
          words64At (sp + 0x9d0#64) dws9d0) ∗ F1) := by
      dsimp only [F0, F1]; ac_rfl
    rwa [← heq]
  have hpc' : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr encryptWithStoresName + 0xe88#64 := by
    unfold storedPC at hpc
    rwa [entryOf_encEntry (C := C) (ctl := ctl) (abs := abs) env.loads] at hpc
  have hwp := finish_stage_sepWP (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (b469 := b469)
    hbws hdws9d0 hcap_lt hpc' hrun hsp_al hsp hx26
  have hexit : SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s (fun _ => False) := by
    refine segExit_of_sepWP hmem_stage hwp ?_
    intro s1 P_f hsteps1 hpc1 hrun1 hmf1
      ⟨hsp1, hsp1_al, htr1, hsym1, hx19_1, hx21_1, hx22_1, hx23_1, hx26_1, hx27_1, hx28_1, hx29_1, _, hvregs1, hPf⟩
    subst hPf
    have hpc1' : s1.pc = encEntry img + 0xef0#64 := by
      rw [entryOf_encEntry (C := C) (ctl := ctl) (abs := abs) env.loads, hpc1]
    have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x (okAnswers r c) (.ok m) s0 s1 :=
      ⟨hm.1, htr1.trans hm.2⟩
    refine segFinish_from_ef0 env x R0 s0 s1 (okAnswers r c) m
      w0 w1 w2 w3 prevCap prevPtr
      G (otr'.applyToSessionState taken) bws dws H hbws hdws hw0_ne hm1 hst ?_
    refine ⟨hpc1', ⟨hrun1, hsp1, hsp0_al, hsp1_al, hx29_1.trans hx29, hx19_1.trans hx19,
      hsteps1.frozenLoaded hfl, hsym1.trans hsym, hvregs1.trans hvregs⟩,
      ⟨hx22_1, hx26_1, hx28_1.trans hx28, hx27_1, hx21_1, hx23_1⟩,
      hstack_le, ?_⟩
    have hmf2 : s1.mem ⊨
        (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
          ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
          words64At (sp + 0x370#64) [w0, w1, w2, w3] ∗
          words64At (sp + 0x390#64) bws ∗
          ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
          memRegion (sp + 0x46a#64) 0x36) ∗
        (sessionStateAt A (sp + 0x128#64) G (otr'.applyToSessionState taken) ∗
         cmScratch sp ∗
         vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
         words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
         words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         encCommon A ctl img x (x.draws S (okAnswers r c)) s0 ∗ R) := by
      have heq :
          (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
            ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
            words64At (sp + 0x370#64) [w0, w1, w2, w3] ∗
            words64At (sp + 0x390#64) bws ∗
            ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
            memRegion (sp + 0x46a#64) 0x36) ∗
          (sessionStateAt A (sp + 0x128#64) G (otr'.applyToSessionState taken) ∗
           cmScratch sp ∗
           vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
           words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
           words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommon A ctl img x (x.draws S (okAnswers r c)) s0 ∗ R) =
          ⌜G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧ G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0⌝ ∗
          ((((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗
            words64At (sp + 0x370#64) [w0, w1, w2, w3] ∗
            words64At (sp + 0x390#64) bws ∗
            ((sp + 0x469#64) ↦₈ 0#8) ∗
            words64At (sp + 0x9d0#64) bws) ∗ F1) := by
        rw [sessionStateAt_unfold_cap A (sp + 0x128#64) G (otr'.applyToSessionState taken)]
        dsimp only [F1]; ac_rfl
      rw [heq, satisfies_pure_sepConj]
      exact ⟨⟨hcap_le, hcap_lt, hptr_nz⟩, hmf1⟩
    have hmf3 := Satisfies.mono
      (sepConj_mono_left (mid_280_to_4a0_weaken sp k w0 w1 w2 w3 bws hbws)) hmf2
    have heq2 :
        (memRegion (sp + 0x280#64) 0x220 ∗
         (sessionStateAt A (sp + 0x128#64) G (otr'.applyToSessionState taken) ∗
          cmScratch sp ∗
          vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
          words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommon A ctl img x (x.draws S (okAnswers r c)) s0 ∗ R)) =
        ((cmScratch sp ∗
          vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          sessionStateAt A (sp + 0x128#64) G (otr'.applyToSessionState taken) ∗
          memRegion (sp + 0x280#64) 0x220 ∗
          words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
          words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         encCommon A ctl img x (x.draws S (okAnswers r c)) s0 ∗ R) := by ac_rfl
    rwa [← heq2]
  exact hexit

theorem segFinish_ok : SegFinishSpec Scope Q C ctl uuidTryParse S encRecord abs (img := img) (A := A) :=
  segFinish_okV

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFinish

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.CommonPlaced
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.ProtocolErrCommon
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Relocatable (`[LibsignalPlacement]`) T5 Protocol-Error Tail Bridges (`ProtocolErrCommonPlaced`)
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr

open Arm64 ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon

set_option maxRecDepth 200000

theorem encTail_placed_run [lsmpl : LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {C : Crypto} {Hk : LibsignalHooks}
    {x : WithStoresEncGhost} {answers : StoreAnswers (List (BitVec 8)) Unit} {pc pc' : BitVec 64}
    {regs regs' : BitVec 64 → State → Prop} {slots slots' Act Fr : BitVec 64 → SepProp}
    {Act' : BitVec 64 → SepProp} {R : SepProp} {s0 s : State}
    (hs : EncTailVPlaced kit st0 ikit ist0 C ctl uuidTryParse S x answers pc regs slots R s0 s)
    (hsplit : ∀ sp, slots sp ⊢ Act sp ∗ Fr sp)
    (hjoin : ∀ sp, Act' sp ∗ Fr sp ⊢ slots' sp)
    (hwp : ∀ sp, s.pc = pc → encMidMetaPlaced x s0 s → regs sp s → sp = s0.sp - 0xbe0#64 →
      SepWP (lsProg_198 Hk) pc' s (Act sp)
        (fun s' P => s'.sp = s.sp ∧ s'.trace = s.trace ∧ s'.readReg64 .x19 = s.readReg64 .x19 ∧
          s'.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs s' = calleeSavedVRegs s ∧ regs' sp s' ∧
          ∀ m F, (m ⊨ P ∗ F) → (m ⊨ Act' sp ∗ F)))
    (hL : (lsProg_198 Hk).CodeLoaded s.mem) :
    ∃ s', Steps (lsProg_198 Hk) s s' ∧ s'.trace = s.trace ∧
      EncTailVPlaced kit st0 ikit ist0 C ctl uuidTryParse S x answers pc' regs' slots' R s0 s' := by
  unfold EncTailVPlaced at hs
  obtain ⟨hpc, hmeta, hregs, hstk, hmem⟩ := hs
  have hmeta' := hmeta
  obtain ⟨hrun, hsp, hsp0al, hspal, hx29, hx19, hcrl, hvregs⟩ := hmeta'
  have hmem2 : s.mem ⊨ Act (s0.sp - 0xbe0#64) ∗ (Fr (s0.sp - 0xbe0#64) ∗
      (encSpillsAtV kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗ memRegion x.ret 248 ∗
        encCommonPlaced A ctl x (x.draws S answers) s0 ∗
        (encStoreExtraPlaced kit (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
          ikit (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2) x s0 ∗ R))) := by
    rw [← sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left (hsplit _)) hmem
  obtain ⟨s', hsteps, ⟨hpc', hrun', P, hmP, hsp', htr', hx19', hx29', hvregs', hregs', hent⟩ | ⟨_, _hoom⟩⟩ :=
    (hwp _ hpc hmeta hregs rfl).elim hmem2 hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  refine ⟨s', hsteps, htr', ?_⟩
  unfold EncTailVPlaced
  refine ⟨hpc', ⟨hrun', hsp'.trans hsp, hsp0al, ?_, hx29'.trans hx29, hx19'.trans hx19,
    hcrl.of_keepsFrozen hsteps.keepsFrozen, hvregs'.trans hvregs⟩, hregs', hstk, ?_⟩
  · unfold State.spAligned at hspal ⊢
    rw [hsp']
    exact hspal
  · have h1 := hent _ _ hmP
    rw [← sepConj_assoc] at h1
    exact Satisfies.mono (sepConj_mono_left (hjoin _)) h1

theorem segExit_placed_of_run [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks} {x : WithStoresEncGhost} {R : SepProp} {s0 s : State}
    {answers : StoreAnswers (List (BitVec 8)) Unit}
    {res : Except (ApiError AddrVal Unit) CiphertextMessage} {next : State → Prop}
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers res s0 s)
    (hrun : (lsProg_198 Hk).CodeLoaded s.mem →
      ∃ s', Steps (lsProg_198 Hk) s s' ∧ s'.trace = s.trace ∧ next s')
    (hnext : ∀ s', TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers res s0 s' → next s' →
      SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s' (fun _ => False)) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s (fun _ => False) := by
  intro hL
  obtain ⟨s', h1, htr, hn⟩ := hrun hL
  obtain ⟨sf, h2, hout⟩ := hnext s' ⟨hm.1, htr.trans hm.2⟩ hn (h1.codeLoaded hL)
  exact ⟨sf, h1.trans h2, hout⟩

theorem encTail_placed_run_withEncCommon [lsmpl : LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {C : Crypto} {Hk : LibsignalHooks}
    {x : WithStoresEncGhost} {answers : StoreAnswers (List (BitVec 8)) Unit} {pc pc' : BitVec 64}
    {regs regs' : BitVec 64 → State → Prop} {slots slots' : BitVec 64 → SepProp}
    {Act Act' Fr : SepProp} {R : SepProp} {s0 s : State}
    (hs : EncTailVPlaced kit st0 ikit ist0 C ctl uuidTryParse S x answers pc regs slots R s0 s)
    (hsplit : slots (s0.sp - 0xbe0#64) ∗ encCommonPlaced A ctl x (x.draws S answers) s0 ⊢ Act ∗ Fr)
    (hjoin : Act' ∗ Fr ⊢ slots' (s0.sp - 0xbe0#64) ∗ encCommonPlaced A ctl x (x.draws S answers) s0)
    (hwp : s.pc = pc → encMidMetaPlaced x s0 s → regs (s0.sp - 0xbe0#64) s →
      SepWP (lsProg_198 Hk) pc' s Act
        (fun s' P => s'.sp = s.sp ∧ s'.trace = s.trace ∧ s'.readReg64 .x19 = s.readReg64 .x19 ∧
          s'.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs s' = calleeSavedVRegs s ∧
          regs' (s0.sp - 0xbe0#64) s' ∧
          ∀ m F, (m ⊨ P ∗ F) → (m ⊨ Act' ∗ F)))
    (hL : (lsProg_198 Hk).CodeLoaded s.mem) :
    ∃ s', Steps (lsProg_198 Hk) s s' ∧ s'.trace = s.trace ∧
      EncTailVPlaced kit st0 ikit ist0 C ctl uuidTryParse S x answers pc' regs' slots' R s0 s' := by
  let R' := encStoreExtraPlaced kit (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
    ikit (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2) x s0 ∗ R
  unfold EncTailVPlaced at hs
  obtain ⟨hpc, hmeta, hregs, hstk, hmem⟩ := hs
  have hmeta' := hmeta
  obtain ⟨hrun, hsp, hsp0al, hspal, hx29, hx19, hcrl, hvregs⟩ := hmeta'
  have hmem2 : s.mem ⊨ Act ∗ (Fr ∗ (encSpillsAtV kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
      memRegion x.ret 248 ∗ R')) := by
    rw [← sepConj_assoc]
    refine Satisfies.mono (sepConj_mono_left hsplit) ?_
    exact Satisfies.mono (Entails.of_eq (by dsimp only [R']; sep_ac_rfl)) hmem
  obtain ⟨s', hsteps, ⟨hpc', hrun', P, hmP, hsp', htr', hx19', hx29', hvregs', hregs', hent⟩ | ⟨_, _hoom⟩⟩ :=
    (hwp hpc hmeta hregs).elim hmem2 hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  refine ⟨s', hsteps, htr', ?_⟩
  unfold EncTailVPlaced
  refine ⟨hpc', ⟨hrun', hsp'.trans hsp, hsp0al, ?_, hx29'.trans hx29, hx19'.trans hx19,
    hcrl.of_keepsFrozen hsteps.keepsFrozen, hvregs'.trans hvregs⟩, hregs', hstk, ?_⟩
  · unfold State.spAligned at hspal ⊢
    rw [hsp']
    exact hspal
  · have h1 := hent _ _ hmP
    rw [← sepConj_assoc] at h1
    have h2 := Satisfies.mono (sepConj_mono_left hjoin) h1
    exact Satisfies.mono (Entails.of_eq (by dsimp only [R']; sep_ac_rfl)) h2

def encCommonPlacedFr [LibsignalPlacement] (A : RustAlloc) (ctl : BitVec 64) (x : WithStoresEncGhost)
    (draws : Nat) (s0 : State) (n : Nat) : SepProp :=
  (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
    nowAt s0.sp x.now ∗ tapeAfter ctl x.cur x.rest draws ∗ FromRecordCallees.lsLogOff ∗
    memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 encSubStack) (encSubStack - n) ∗
    encSavedRegs s0.sp s0

theorem encCommonPlaced_eq [LibsignalPlacement] (A : RustAlloc) (ctl : BitVec 64) (x : WithStoresEncGhost)
    (draws : Nat) (s0 : State) (n : Nat) (hn : n ≤ encSubStack) :
    encCommonPlaced A ctl x draws s0 =
      (A.pool ∗ stackAt (s0.sp - 0xbe0#64) n) ∗ encCommonPlacedFr A ctl x draws s0 n := by
  have h := stackAt_split_bottom (s0.sp - 0xbe0#64) n (encSubStack - n) (by
    simp only [encSubStack, withStoresEncStack, entryStack, encFrameSize] at hn ⊢; omega)
  rw [show n + (encSubStack - n) = encSubStack by omega] at h
  unfold encCommonPlaced encCommonPlacedFr
  rw [h]
  sep_ac_rfl

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails.ProtocolErr

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.TrapBridge
public import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtEncryptBody
public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalSpqrV1.Statements
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Top
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopPhase3
import LibsignalBinary.Proofs.Cli.TripleRatchet.Encrypt.Core
import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtCtPkEq
import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtGenKeysMac
import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtHmacX
import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtSignalMsgNew
import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtSpqrSendEmpty
import LibsignalBinary.Proofs.Cli.TripleRatchet.Glue
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.NewFromSlice
import LibsignalBinary.Proofs.TripleRatchet.Glue
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Expand
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Extract
import LibsignalBinary.Proofs.TripleRatchet.Keys.GenerateKeys
import LibsignalBinary.Proofs.TripleRatchet.Mac.Addresses
import LibsignalBinary.Proofs.TripleRatchet.Wire.New
import LibsignalBinary.Proofs.SpqrV1.M4.Encrypt -- shake: keep

/-!
# CLI SPQR V1 `OutgoingTripleRatchet::encrypt` Assembly

Threads spatial frames and pure state/tape predicates through `spqr::send` to prove
`OutgoingTripleRatchet::encrypt::<Coins>` against `otrEncryptSpecT` across fixed-table,
`trTrapProgAt`, and `tripleRatchetProgAtExt` programs.
-/

@[expose] public section

namespace CryptoVerification.LibsignalSpqrV1.M4

set_option autoImplicit false

open Arm64 ProofLib CryptoGames CryptoGames.CBC CryptoGames.HMAC CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalTripleRatchet.Encrypt

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem h43a_except_ok_eq_error {α ε : Type _} (x : α) (e : ε) :
    ((Except.ok x : Except ε α) = Except.error e) = False := by simp

private theorem h43a_except_ok_ne_error_eq_true {α ε : Type _} (x : α) (e : ε) :
    ((Except.ok x : Except ε α) ≠ Except.error e) = True := by simp

attribute [local arm64_norm] h43a_except_ok_eq_error h43a_except_ok_ne_error_eq_true

private theorem h43a_subroutine_ok_of_sepWPp {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} {Qpre : α → State → SepProp} {F : SepProp}
    (h : ∀ (x : α) (R : SepProp) (s0 : State), s0.pc = entry → s0.status = .Running →
      (s0.mem ⊨ (Qpre x s0 ∗ F ∗ spec.pre x s0) ∗ R) → s0.spAligned = true →
      ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
        SepWPp prog (s0.readReg64 Reg.lr) s0 P
          (fun sf P_f => ((sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ spec.post x s0 sf ∗ (F ∗ R))) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ spec.onPanic x s0 sf ∗ R))) :
    subroutine_ok prog entry
      { spec with
        pre := fun x s => Qpre x s ∗ F ∗ spec.pre x s
        post := fun x s0 sf => F ∗ spec.post x s0 sf } := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp
  obtain ⟨P, Fr, hm, hwp⟩ := h x R s0 hpc hrun hpre hsp
  refine ⟨P, Fr, hm, ?_⟩
  have hcomm : ∀ sf, (F ∗ spec.post x s0 sf) ∗ R = spec.post x s0 sf ∗ (F ∗ R) := fun sf => by ac_rfl
  simp only [hcomm]
  exact hwp

private theorem h43a_absorb_frame {prog : Program} {ret : BitVec 64} {s : State}
    {F P R : SepProp} {Ψ φ_pan : State → Prop} {sp0 : BitVec 64} {s0 : State}
    (h : SepWPp prog ret s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ (F ∗ R)) → Ψ sf) ∧
        sf.sp = sp0 ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ (F ∗ R)) → (φ_pan sf ∧ sf.mem ⊨ anyHeap ∗ (F ∗ R)))) :
    SepWPp prog ret s (F ∗ P)
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → Ψ sf) ∧
        sf.sp = sp0 ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (φ_pan sf ∧ sf.mem ⊨ anyHeap ∗ R)) := by
  intro R' hm hL
  have hm' : s.mem ⊨ P ∗ (F ∗ R') := by
    have heq : (F ∗ P) ∗ R' = P ∗ (F ∗ R') := by ac_rfl
    exact heq ▸ hm
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hq, hsp, hcs⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hfalse⟩⟩ :=
    h (F ∗ R') hm' hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpc, hrun, F ∗ P_f, ?_, ⟨?_, hsp, hcs⟩⟩⟩
    · have heq : P_f ∗ (F ∗ R') = (F ∗ P_f) ∗ R' := by ac_rfl
      exact heq ▸ hmf
    · intro hmR
      have heq : (F ∗ P_f) ∗ R = P_f ∗ (F ∗ R) := by ac_rfl
      exact hq (heq ▸ hmR)
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, F ∗ P_f, ?_, ?_⟩)⟩
    · have heq : P_f ∗ (F ∗ R') = (F ∗ P_f) ∗ R' := by ac_rfl
      exact heq ▸ hmf
    · intro hmR
      have heq : (F ∗ P_f) ∗ R = P_f ∗ (F ∗ R) := by ac_rfl
      obtain ⟨hφ, hany⟩ := hqp (heq ▸ hmR)
      refine ⟨hφ, ?_⟩
      rw [← sepConj_assoc] at hany
      exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hany
  · exact (not_satisfies_false_sepConj hfalse).elim

set_option maxHeartbeats 600000 in
set_option maxRecDepth 4096 in
set_option linter.unusedSimpArgs false in
/-- `otrEncrypt_body_ok_ext` generalized with a pure predicate `Q` on state/tape and a spatial
frame `F` threaded through `spqr::send`. -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.M4.otrEncrypt_body_ok_ext_frame (Q : List (BitVec 8) → List (BitVec 8) → Prop) (F : SepProp)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (ext : String → Option (State → State)) (img : Obj.Image)
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hSend : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendName)
      { CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendSpec A ctl S img with
        pre := fun x s => ⌜Q x.st.bytes x.rest⌝ ∗ F ∗ (CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendSpec A ctl S img).pre x s
        post := fun x s0 sf => F ∗ (CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendSpec A ctl S img).post x s0 sf })
    (hMK : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr messageKeysName) (messageKeysSpec C.F A img))
    (hGK : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr generateKeysName)
      ((generateKeysSpec C.F A).inImage img))
    (hNew : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signalMessageNewName)
      ((signalMessageNewSpec C.F A uuidTryParse).inImage img))
    (hNCK : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr nextChainKeyName) (nextChainKeySpec C.F img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
      { CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptSpec C A ctl uuidTryParse S img with
        pre := fun x s =>
          ⌜Q x.ot.pqrState x.rest⌝ ∗ F ∗ (CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptSpec C A ctl uuidTryParse S img).pre x s
        post := fun x s0 sf => F ∗ (CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptSpec C A ctl uuidTryParse S img).post x s0 sf } :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt.otrEncrypt_body_ok_ext_frame
    Q F C A ctl S ext img hC himg hSend hMK hGK hNew hNCK

/-- Specialization of `otrEncrypt_body_ok_ext_frame` to `tripleRatchetProgAt`. -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.M4.otrEncrypt_body_ok_frame (Q : List (BitVec 8) → List (BitVec 8) → Prop) (F : SepProp)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image)
    (hHooks : TripleRatchetHooks C A S abs)
    (himg : Obj.Loads libsignalSessionImage img)
    (hSend : subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendName)
      { CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendSpec A ctl S img with
        pre := fun x s => ⌜Q x.st.bytes x.rest⌝ ∗ F ∗ (CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendSpec A ctl S img).pre x s
        post := fun x s0 sf => F ∗ (CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendSpec A ctl S img).post x s0 sf })
    (hMK : MessageKeysOk img C A ctl abs)
    (hGK : GenerateKeysOk img C A ctl abs)
    (hNew : SignalMessageNewOk img C A ctl uuidTryParse abs)
    (hNCK : NextChainKeyOk img C ctl abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
      { CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptSpec C A ctl uuidTryParse S img with
        pre := fun x s =>
          ⌜Q x.ot.pqrState x.rest⌝ ∗ F ∗ (CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptSpec C A ctl uuidTryParse S img).pre x s
        post := fun x s0 sf => F ∗ (CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptSpec C A ctl uuidTryParse S img).post x s0 sf } :=
  CryptoVerification.Cli.LibsignalSpqrV1.M4.otrEncrypt_body_ok_ext_frame Q F C A ctl S (tripleRatchetExterns C ctl abs) img
    (Stage2Contracts.of_tripleRatchetProgAt img.base C A ctl S abs hHooks) himg hSend hMK hGK hNew hNCK

/-- `OTR::encrypt` satisfies `otrEncryptSpecT` for any `SpqrModel` `S` whose `spqr::send` satisfies
`spqrSendSpecT`. -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.M4.otrEncryptT_run_of_send (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image)
    (hHooks : TripleRatchetHooks C A S abs)
    (himg : Obj.Loads libsignalSessionImage img)
    (hSend : subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendName)
      (CryptoVerification.Cli.LibsignalSpqrV1.spqrSendSpecT A ctl S img))
    (hMK : MessageKeysOk img C A ctl abs)
    (hGK : GenerateKeysOk img C A ctl abs)
    (hNew : SignalMessageNewOk img C A ctl uuidTryParse abs)
    (hNCK : NextChainKeyOk img C ctl abs) :
    subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.otrEncryptSpecT C A ctl uuidTryParse S img) := by
  apply root_of_tripleRatchetProgAt himg
  rw [tripleRatchetProg_eq_tripleRatchetProgAt himg,
    entryOf_eq_tripleRatchetProgAt (C := C) (ctl := ctl) (abs := abs) himg CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendName] at hSend
  exact CryptoVerification.Cli.LibsignalSpqrV1.M4.otrEncrypt_body_ok_frame (fun pq rest => pq.length < 2 ^ 32 ∧ 64 ≤ rest.length)
    (TokenInit img) C A ctl S abs img hHooks himg hSend hMK hGK hNew hNCK

/-- `OtrEncryptV1RunStmt` follows from `SpqrSendV1Stmt`. -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.M4.otrEncryptV1_run_of_sendV1 (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (K : MlKem)
    (abs : String → Option (State → State)) (img : Obj.Image)
    (hSendV1 : CryptoVerification.Cli.LibsignalSpqrV1.SpqrSendV1Stmt C A ctl K abs img) :
    CryptoVerification.Cli.LibsignalSpqrV1.OtrEncryptV1RunStmt C A ctl K abs img := by
  intro hHooks hSpqr himg
  obtain ⟨hMK, hGK, hNew, hNCK⟩ :=
    CryptoVerification.LibsignalTripleRatchet.Statements.encryptCallees C A ctl (spqrV1 C.F K) abs img hHooks himg
  exact CryptoVerification.Cli.LibsignalSpqrV1.M4.otrEncryptT_run_of_send C A ctl (spqrV1 C.F K) abs img hHooks himg
    (hSendV1 hHooks hSpqr himg) hMK hGK hNew hNCK

/-! ## 1. Trap-at-RNG (`trTrapProgAt`) Encrypt Contracts -/

open CryptoVerification.LibsignalSpqrV1 (MlKem SpqrHooks spqrV1)

/-- Statement that `spqr::send::<Coins>` meets `spqrSendSpecT` on `trTrapProgAt img.base C abs`
    without any `rngFill` hook. -/
def _root_.CryptoVerification.Cli.LibsignalSpqrV1.M4.SpqrSendV1Stmt_trap
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (K : MlKem)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A (spqrV1 C.F K) abs →
  SpqrHooks C A K abs →
  Obj.Loads libsignalSessionImage img →
    subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendName)
      (CryptoVerification.Cli.LibsignalSpqrV1.spqrSendSpecT A ctl (spqrV1 C.F K) img)

/-- Statement that `OutgoingTripleRatchet::encrypt::<Coins>` meets `otrEncryptSpecT` on
    `trTrapProgAt img.base C abs` (no `rngFill` hook required). -/
def _root_.CryptoVerification.Cli.LibsignalSpqrV1.M4.OtrEncryptV1RunStmt_trap
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (K : MlKem)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A (spqrV1 C.F K) abs →
  SpqrHooks C A K abs →
  Obj.Loads libsignalSessionImage img →
    subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.otrEncryptSpecT C A ctl uuidTryParse (spqrV1 C.F K) img)

/-- Image-root (`tripleRatchetProg_trap img C abs`) variant of `OtrEncryptV1RunStmt_trap`. -/
def _root_.CryptoVerification.Cli.LibsignalSpqrV1.M4.OtrEncryptV1RootRunStmt_trap
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (K : MlKem)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A (spqrV1 C.F K) abs →
  SpqrHooks C A K abs →
  Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProg_trap img C abs)
      (entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.otrEncryptSpecT C A ctl uuidTryParse (spqrV1 C.F K) img)

/-- The four callee contracts of `OTR::encrypt` on `trTrapExterns C abs` (`trTrapProgAt img.base C abs`),
    instantiated directly from `Stage2Contracts_trap` and the `*_ext` lemmas without `rng_fill`. -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.M4.encryptCallees_trap
    (C : Crypto) (A : RustAlloc) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image)
    (hHooks : TripleRatchetHooks C A S abs)
    (himg : Obj.Loads libsignalSessionImage img) :
    MessageKeysOkExt img C.F A (trTrapExterns C abs) ∧
    GenerateKeysOkExt img C A (trTrapExterns C abs) ∧
    SignalMessageNewOkExt img C A uuidTryParse (trTrapExterns C abs) ∧
    NextChainKeyOkExt img C.F (trTrapExterns C abs) := by
  have hC : Stage2Contracts_trap img.base C A uuidTryParse S (trTrapExterns C abs) :=
    Stage2Contracts_trap.of_tripleRatchetProgAt_trap img.base C A S abs hHooks
  have hle := CryptoVerification.Cli.SpqrV1.Top.Send.sessionExterns_le_trTrap C abs
  have : HkdfHooks C.F (trTrapExterns C abs) := HkdfHooks.of_le_sessionExterns hle
  have hNewSlice := ConsumeMessageKeyTransfer.new_from_slice_ok_ext img C.F himg hle
  have hPkSer := Glue.publicKeySerializeOk_ext hC.toAllocContracts
  exact
    ⟨Glue.messageKeysOk_ext hC.toAllocContracts hle himg,
     Keys.generateKeys_ok_ext himg
       (extract_ok_ext img C (trTrapExterns C abs) hNewSlice)
       (expand_multi_info_ok_ext img.base C (trTrapExterns C abs))
       hC.toAllocContracts,
     signalMessageNew_ok_ext hC.toAllocContracts hPkSer
       (Glue.encodedLenOk_ext img.base A (trTrapExterns C abs))
       (Glue.encode_varint_ok_ext hC.toAllocContracts)
       (serializeAddresses_subroutine_ok_of_contracts img.base A (trTrapExterns C abs)
         hC.toAllocContracts hC.uuid_try_parse)
       (computeMac_subroutine_ok_of_contracts img C A (trTrapExterns C abs)
         hC.toAllocContracts hC.compress256 hNewSlice hPkSer),
     Glue.nextChainKeyOk_ext hle himg⟩

/-- `OTR::encrypt::<Coins>` meets `otrEncryptSpecT` on `trTrapProgAt img.base C abs` at any `S` whose
    `spqr::send::<Coins>` meets `spqrSendSpecT` on `trTrapProgAt img.base C abs`. -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.M4.otrEncryptT_run_of_send_trap
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image)
    (hHooks : TripleRatchetHooks C A S abs)
    (himg : Obj.Loads libsignalSessionImage img)
    (hSend : subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendName)
      (CryptoVerification.Cli.LibsignalSpqrV1.spqrSendSpecT A ctl S img))
    (hMK : MessageKeysOkExt img C.F A (trTrapExterns C abs))
    (hGK : GenerateKeysOkExt img C A (trTrapExterns C abs))
    (hNew : SignalMessageNewOkExt img C A uuidTryParse (trTrapExterns C abs))
    (hNCK : NextChainKeyOkExt img C.F (trTrapExterns C abs)) :
    subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.otrEncryptSpecT C A ctl uuidTryParse S img) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt.otrEncrypt_body_ok_frame_trap
    (fun pq rest => pq.length < 2 ^ 32 ∧ 64 ≤ rest.length)
    (TokenInit img) C A ctl S abs img hHooks himg hSend hMK hGK hNew hNCK

/-- `OtrEncryptV1RunStmt_trap` from `SpqrSendV1Stmt_trap`. -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.M4.otrEncryptV1_run_of_sendV1_trap
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (K : MlKem)
    (abs : String → Option (State → State)) (img : Obj.Image)
    (hSendV1 : CryptoVerification.Cli.LibsignalSpqrV1.M4.SpqrSendV1Stmt_trap C A ctl K abs img) :
    CryptoVerification.Cli.LibsignalSpqrV1.M4.OtrEncryptV1RunStmt_trap C A ctl K abs img := by
  intro hHooks hSpqr himg
  obtain ⟨hMK, hGK, hNew, hNCK⟩ :=
    CryptoVerification.Cli.LibsignalSpqrV1.M4.encryptCallees_trap C A (spqrV1 C.F K) abs img hHooks himg
  exact CryptoVerification.Cli.LibsignalSpqrV1.M4.otrEncryptT_run_of_send_trap C A ctl (spqrV1 C.F K) abs img
    hHooks himg (hSendV1 hHooks hSpqr himg) hMK hGK hNew hNCK

/-- Unconditional SPQR V1 `OutgoingTripleRatchet::encrypt::<Coins>` verification on
    `trTrapProgAt img.base C abs` (no `rngFill` hook required; discharges `spqr::send::<Coins>` via
    `CryptoVerification.Cli.SpqrV1.Top.Send.spqr_send_ok_trTrap`). -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.M4.otrEncryptV1_run_trap
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (K : CryptoVerification.LibsignalSpqrV1.MlKem)
    (abs : String → Option (State → State)) (img : Obj.Image)
    (hHooks : TripleRatchetHooks C A (CryptoVerification.LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hSpqr : CryptoVerification.LibsignalSpqrV1.SpqrHooks C A K abs)
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.otrEncryptSpecT C A ctl uuidTryParse
        (CryptoVerification.LibsignalSpqrV1.spqrV1 C.F K) img) :=
  CryptoVerification.Cli.LibsignalSpqrV1.M4.otrEncryptV1_run_of_sendV1_trap C A ctl K abs img
    (CryptoVerification.Cli.SpqrV1.Top.Send.spqr_send_ok_trTrap C A ctl K abs img)
    hHooks hSpqr himg

/-- Image-root (`tripleRatchetProg_trap img C abs`) corollary of `otrEncryptV1_run_trap`. -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.M4.otrEncryptV1_root_run_trap
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (K : CryptoVerification.LibsignalSpqrV1.MlKem)
    (abs : String → Option (State → State)) (img : Obj.Image) :
    CryptoVerification.Cli.LibsignalSpqrV1.M4.OtrEncryptV1RootRunStmt_trap C A ctl K abs img :=
  fun hHooks hSpqr himg =>
    root_of_tripleRatchetProgAt_trap himg
      (CryptoVerification.Cli.LibsignalSpqrV1.M4.otrEncryptV1_run_trap C A ctl K abs img hHooks hSpqr himg)

/-! ## 2. Contract-Backed (`tripleRatchetProgAtExt`) Encrypt Contracts -/

/-- Statement that `spqr::send::<Coins>` meets `spqrSendSpecT` on `tripleRatchetProgAtExt img.base ext`. -/
def _root_.CryptoVerification.Cli.LibsignalSpqrV1.M4.SpqrSendV1Stmt_ext
    (A : RustAlloc) (ctl : BitVec 64) (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State)) (img : Obj.Image) : Prop :=
  Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendName)
      (CryptoVerification.Cli.LibsignalSpqrV1.spqrSendSpecT A ctl (spqrV1 F K) img)

/-- Statement that `OutgoingTripleRatchet::encrypt::<Coins>` meets `otrEncryptSpecT` on
    `tripleRatchetProgAtExt img.base ext`. -/
def _root_.CryptoVerification.Cli.LibsignalSpqrV1.M4.OtrEncryptV1RunStmt_ext
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (K : MlKem)
    (ext : String → Option (State → State)) (img : Obj.Image) : Prop :=
  Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.otrEncryptSpecT C A ctl uuidTryParse (spqrV1 C.F K) img)

/-- Statement that `OutgoingTripleRatchet::encrypt::<Coins>` meets `otrEncryptSpecQExt (· = [])` on
    `tripleRatchetProgAtExt img.base ext`. -/
def _root_.CryptoVerification.Cli.LibsignalSpqrV1.M4.OtrEncryptEmptyRunStmt_ext
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (ext : String → Option (State → State)) (img : Obj.Image) : Prop :=
  S.SendEmptyOk →
  Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
      { CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptSpec C A ctl uuidTryParse S img with
        pre := fun x s => ⌜(· = []) x.ot.pqrState⌝ ∗
          (CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptSpec C A ctl uuidTryParse S img).pre x s }

section CliExtEncrypt

open CryptoVerification.SignalSession (CliExternsOk cliExternsWith)
open CryptoVerification.SignalSession.Cli.Slots
  (AgreeOnCliHooks trapUnlisted cliExternsWith_trapUnlisted cliExternsOk_trapUnlisted
   allocContractsX_of_externsOk_on stage2ContractsWeak_of_externsOk_on)

/-- Stacked callee bundle (`MessageKeysOkX`, `GenerateKeysOkExtStacked`, `SignalMessageNewOkExt32`,
`NextChainKeyOkX`) for `OTR::encrypt::<Coins>` on `tripleRatchetProgAtExt img.base ext`. -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.M4.encryptCallees_ext
    (C : Crypto) (A : RustAlloc) (ext : String → Option (State → State)) (img : Obj.Image)
    (himg : Obj.Loads libsignalSessionImage img)
    (hAX : AllocContractsX img A ext)
    (hA4K : CryptoVerification.Cli.LibsignalSpqrV1.M4.AllocContracts4K img.base A ext)
    (h_comp : HookSat ext compress256Name (withStack (compress256Spec C.F) extHookStack))
    (hHkdf : HkdfContractsExt img C.F ext) :
    MessageKeysOkX img C.F A ext ∧
    CryptoVerification.Cli.LibsignalTripleRatchet.ExtEncryptBody.GenerateKeysOkExtStacked img C A ext ∧
    CryptoVerification.Cli.LibsignalTripleRatchet.ExtEncryptBody.SignalMessageNewOkExt32 img C A uuidTryParse ext ∧
    CryptoVerification.Cli.LibsignalTripleRatchet.ExtCallees.NextChainKeyOkX img C.F ext := by
  have hhmac :=
    CryptoVerification.Cli.LibsignalTripleRatchet.ExtHmacX.hmac_sha256_ok_of_hkdfContracts
      (C := C) himg hHkdf
  exact
    ⟨CryptoVerification.Cli.LibsignalTripleRatchet.Glue.messageKeys_ok_of_hmacX hAX hhmac,
     CryptoVerification.Cli.LibsignalTripleRatchet.ExtGenKeysMac.generateKeys_ok_stacked_ext_x
       himg hHkdf hAX,
     CryptoVerification.Cli.LibsignalTripleRatchet.ExtSignalMsgNew.signalMessageNew_ok_of_contracts_ext32
       himg hAX hA4K h_comp hHkdf,
     CryptoVerification.Cli.LibsignalTripleRatchet.ExtCallees.nextChainKey_ok_of_hmacX hhmac⟩

/-- Stacked callee bundle for `OTR::encrypt::<Coins>` from `CliExternsOk P A ext` on any `ext'`
agreeing with `ext` on `cliHookNames`. -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.M4.encryptCallees_ext_on
    {P : E2E.PEParams} {A : RustAlloc}
    {ext ext' : String → Option (State → State)} (img : Obj.Image)
    (hOk : CliExternsOk P A ext) (hAg : AgreeOnCliHooks ext ext')
    (himg : Obj.Loads libsignalSessionImage img) :
    MessageKeysOkX img P.C.F A ext' ∧
    CryptoVerification.Cli.LibsignalTripleRatchet.ExtEncryptBody.GenerateKeysOkExtStacked img P.C A ext' ∧
    CryptoVerification.Cli.LibsignalTripleRatchet.ExtEncryptBody.SignalMessageNewOkExt32 img P.C A uuidTryParse ext' ∧
    CryptoVerification.Cli.LibsignalTripleRatchet.ExtCallees.NextChainKeyOkX img P.C.F ext' :=
  CryptoVerification.Cli.LibsignalSpqrV1.M4.encryptCallees_ext P.C A ext' img himg
    (allocContractsX_of_externsOk_on hOk hAg img)
    (CryptoVerification.Cli.LibsignalSpqrV1.M4.AllocContracts4K.of_externsOk_on hOk hAg img.base)
    (CryptoVerification.Cli.LibsignalTripleRatchet.ExtCtPkEq.hookSat_compress256_of_externsOk_on hOk hAg)
    (CryptoVerification.Cli.LibsignalTripleRatchet.ExtCtPkEq.hkdfContractsExt_of_externsOk_on img hOk hAg)

/-- `OTR::encrypt::<Coins>` meets `otrEncryptSpecT` on `tripleRatchetProgAtExt img.base ext` from
`Stage2ContractsWeak`, `AllocContracts4K`, `spqrSendSpecT`, and the four stacked callees. -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.M4.otrEncryptT_run_of_send_ext
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (ext : String → Option (State → State)) (img : Obj.Image)
    (hC : Stage2ContractsWeak img C A ext)
    (hA4K : CryptoVerification.Cli.LibsignalSpqrV1.M4.AllocContracts4K img.base A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hSend : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendName)
      (CryptoVerification.Cli.LibsignalSpqrV1.spqrSendSpecT A ctl S img))
    (hMK : MessageKeysOkX img C.F A ext)
    (hGK : CryptoVerification.Cli.LibsignalTripleRatchet.ExtEncryptBody.GenerateKeysOkExtStacked img C A ext)
    (hNew : CryptoVerification.Cli.LibsignalTripleRatchet.ExtEncryptBody.SignalMessageNewOkExt32 img C A uuidTryParse ext)
    (hNCK : CryptoVerification.Cli.LibsignalTripleRatchet.ExtCallees.NextChainKeyOkX img C.F ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.otrEncryptSpecT C A ctl uuidTryParse S img) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.ExtEncryptBody.otrEncrypt_body_ok_ext_frame_x
    (fun pq rest => pq.length < 2 ^ 32 ∧ 64 ≤ rest.length)
    (TokenInit img) C A ctl S ext img hC hA4K himg hSend hMK hGK hNew hNCK

/-- `OtrEncryptV1RunStmt_ext` from `SpqrSendV1Stmt_ext` under `CliExternsOk P A ext` on any `ext'`
satisfying `AgreeOnCliHooks ext ext'`. -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.M4.otrEncryptV1_run_of_sendV1_ext_on
    {P : E2E.PEParams} {A : RustAlloc} {ctl : BitVec 64}
    {ext ext' : String → Option (State → State)} {img : Obj.Image}
    (hOk : CliExternsOk P A ext) (hAg : AgreeOnCliHooks ext ext')
    (hSendV1 : CryptoVerification.Cli.LibsignalSpqrV1.M4.SpqrSendV1Stmt_ext A ctl P.C.F P.Q.K ext' img) :
    CryptoVerification.Cli.LibsignalSpqrV1.M4.OtrEncryptV1RunStmt_ext P.C A ctl P.Q.K ext' img := by
  intro himg
  obtain ⟨hMK, hGK, hNew, hNCK⟩ :=
    CryptoVerification.Cli.LibsignalSpqrV1.M4.encryptCallees_ext_on img hOk hAg himg
  exact CryptoVerification.Cli.LibsignalSpqrV1.M4.otrEncryptT_run_of_send_ext
    P.C A ctl (spqrV1 P.C.F P.Q.K) ext' img
    (stage2ContractsWeak_of_externsOk_on hOk hAg img)
    (CryptoVerification.Cli.LibsignalSpqrV1.M4.AllocContracts4K.of_externsOk_on hOk hAg img.base)
    himg (hSendV1 himg) hMK hGK hNew hNCK

/-- Specialization of `otrEncryptV1_run_of_sendV1_ext_on` to `cliExternsWith ext`. -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.M4.otrEncryptV1_run_of_sendV1_cli_ext
    {P : E2E.PEParams} {A : RustAlloc} {ctl : BitVec 64}
    {ext : String → Option (State → State)} {img : Obj.Image}
    (hOk : CliExternsOk P A ext)
    (hSendV1 : CryptoVerification.Cli.LibsignalSpqrV1.M4.SpqrSendV1Stmt_ext
      A ctl P.C.F P.Q.K (cliExternsWith ext) img) :
    CryptoVerification.Cli.LibsignalSpqrV1.M4.OtrEncryptV1RunStmt_ext
      P.C A ctl P.Q.K (cliExternsWith ext) img :=
  CryptoVerification.Cli.LibsignalSpqrV1.M4.otrEncryptV1_run_of_sendV1_ext_on
    hOk (AgreeOnCliHooks.cliExternsWith ext) hSendV1

/-- Unconditional `OtrEncryptEmptyRunStmt_ext` (`otrEncryptSpecQ (· = [])`) under
`CliExternsOk P A ext` on any `ext'` satisfying `AgreeOnCliHooks ext ext'`. -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.M4.otrEncryptEmpty_run_ext_on
    {P : E2E.PEParams} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {ext ext' : String → Option (State → State)} {img : Obj.Image}
    (hOk : CliExternsOk P A ext) (hAg : AgreeOnCliHooks ext ext') :
    CryptoVerification.Cli.LibsignalSpqrV1.M4.OtrEncryptEmptyRunStmt_ext P.C A ctl S ext' img := by
  intro hE himg
  obtain ⟨hMK, hGK, hNew, hNCK⟩ :=
    CryptoVerification.Cli.LibsignalSpqrV1.M4.encryptCallees_ext_on img hOk hAg himg
  exact CryptoVerification.Cli.LibsignalTripleRatchet.ExtEncryptBody.otrEncrypt_body_ok_ext_x
    (· = []) P.C A ctl S ext' img
    (stage2ContractsWeak_of_externsOk_on hOk hAg img)
    (CryptoVerification.Cli.LibsignalSpqrV1.M4.AllocContracts4K.of_externsOk_on hOk hAg img.base)
    himg
    (CryptoVerification.Cli.LibsignalTripleRatchet.ExtSpqrSendEmpty.spqrSendEmpty_base_of_externsOk_on
      hOk hAg hE)
    hMK hGK hNew hNCK

/-- Unconditional `OtrEncryptEmptyRunStmt_ext` on `cliExternsWith ext` under `CliExternsOk P A ext`. -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.M4.otrEncryptEmpty_run_cli_ext
    {P : E2E.PEParams} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)} {img : Obj.Image}
    (hOk : CliExternsOk P A ext) :
    CryptoVerification.Cli.LibsignalSpqrV1.M4.OtrEncryptEmptyRunStmt_ext
      P.C A ctl S (cliExternsWith ext) img :=
  CryptoVerification.Cli.LibsignalSpqrV1.M4.otrEncryptEmpty_run_ext_on
    hOk (AgreeOnCliHooks.cliExternsWith ext)

/-- Specialization of `otrEncryptV1_run_of_sendV1_cli_ext` to `trapUnlisted ext`. -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.M4.otrEncryptV1_run_of_sendV1_trapUnlisted
    {P : E2E.PEParams} {A : RustAlloc} {ctl : BitVec 64}
    {ext : String → Option (State → State)} {img : Obj.Image}
    (hOk : CliExternsOk P A ext)
    (hSendV1 : CryptoVerification.Cli.LibsignalSpqrV1.M4.SpqrSendV1Stmt_ext
      A ctl P.C.F P.Q.K (trapUnlisted ext) img) :
    CryptoVerification.Cli.LibsignalSpqrV1.M4.OtrEncryptV1RunStmt_ext
      P.C A ctl P.Q.K (trapUnlisted ext) img := by
  rw [← cliExternsWith_trapUnlisted ext] at hSendV1 ⊢
  exact CryptoVerification.Cli.LibsignalSpqrV1.M4.otrEncryptV1_run_of_sendV1_cli_ext
    (cliExternsOk_trapUnlisted hOk) hSendV1

/-- Unconditional `OtrEncryptEmptyRunStmt_ext` on `trapUnlisted ext` under `CliExternsOk P A ext`. -/
theorem _root_.CryptoVerification.Cli.LibsignalSpqrV1.M4.otrEncryptEmpty_run_trapUnlisted
    {P : E2E.PEParams} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)} {img : Obj.Image}
    (hOk : CliExternsOk P A ext) :
    CryptoVerification.Cli.LibsignalSpqrV1.M4.OtrEncryptEmptyRunStmt_ext
      P.C A ctl S (trapUnlisted ext) img := by
  rw [← cliExternsWith_trapUnlisted ext]
  exact CryptoVerification.Cli.LibsignalSpqrV1.M4.otrEncryptEmpty_run_cli_ext
    (cliExternsOk_trapUnlisted hOk)

end CliExtEncrypt

end CryptoVerification.LibsignalSpqrV1.M4

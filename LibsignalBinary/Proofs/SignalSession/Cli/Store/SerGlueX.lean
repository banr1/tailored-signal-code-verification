/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DropSsLocal1Ext
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.HSerX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.RecordSerializeExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionCloneX
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarint

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.SerGlueX

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet

theorem stage1XAllocContractsX_of_trAllocContractsX {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hA : CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A ext) :
    Proofs.libsignal.Stage1X.AllocContractsX img A ext where
  alloc := by
    refine Proofs.libsignal.Hooks2.subroutine_ok_inImage_map' hA.alloc fun ⟨size, align⟩ R s0 hpre => ?_
    refine ⟨(size, align), R, ?_, fun sf hpost => ?_⟩
    · simp only [CryptoVerification.LibsignalTripleRatchet.rustAllocSpecWithStack,
        Proofs.libsignal.Stage1X.rustAllocSpecWithStack] at hpre ⊢
      exact hpre
    · simp only [CryptoVerification.LibsignalTripleRatchet.rustAllocSpecWithStack,
        Proofs.libsignal.Stage1X.rustAllocSpecWithStack] at hpost ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  dealloc := by
    refine Proofs.libsignal.Hooks2.subroutine_ok_inImage_map' hA.dealloc fun ⟨p, size, align⟩ R s0 hpre => ?_
    refine ⟨(p, size, align), R, ?_, fun sf hpost => ?_⟩
    · simp only [CryptoVerification.LibsignalTripleRatchet.rustDeallocExternSpecWithStack,
        Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack] at hpre ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
    · simp only [CryptoVerification.LibsignalTripleRatchet.rustDeallocExternSpecWithStack,
        Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack] at hpost ⊢
      exact hpost
  realloc := by
    refine Proofs.libsignal.Hooks2.subroutine_ok_inImage_map' hA.realloc
      fun ⟨p, old_size, align, new_size, bs⟩ R s0 hpre => ?_
    refine ⟨(p, old_size, align, new_size, bs), R, ?_, fun sf hpost => ?_⟩
    · simp only [CryptoVerification.LibsignalTripleRatchet.rustReallocExternSpecWithStack,
        Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack,
        sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      obtain ⟨⟨hx0, hx1, hx2, hx3, hbs1, hbs2, hlay_old, hlay_new⟩, hmem⟩ := hpre
      exact ⟨⟨hx0, hx1, hx2, hx3, hlay_old, hlay_new, hbs1, hbs2⟩,
        Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem⟩
    · simp only [CryptoVerification.LibsignalTripleRatchet.rustReallocExternSpecWithStack,
        CryptoVerification.LibsignalTripleRatchet.rustReallocSpecWithStack,
        Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack,
        Proofs.libsignal.Stage1X.rustReallocSpecWithStack] at hpost ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  shim := hA.shim extHookStack (Nat.le_refl _) (by decide)
  session_memmove := hA.session_memmove extHookStack (Nat.le_refl _) (by decide)

theorem serContractsX_of_trAllocContractsX {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hA : CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A ext) :
    Proofs.libsignal.Hooks2.SerContractsX img A ext where
  alloc := stage1XAllocContractsX_of_trAllocContractsX hA
  memcpy := Proofs.libsignal.Hooks2.sub_ok_at_of_fnAddr
    (Proofs.libsignal.Hooks2.SP2Ext_fnAddr img.base ext memcpyName)
    (hA.session_memcpy extHookStack (Nat.le_refl _) (by decide))

theorem serializeCanonX_ok_of_trAllocContractsX {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hA : CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.E2E.Record.Serialization.serializeName)
      ((Proofs.libsignal.Hooks2.serializeCanonSpecX A).inImage img) := by
  have hC := serContractsX_of_trAllocContractsX hA
  have hClone := CryptoVerification.E2E.Record.Serialization.sessionClone_ok_ext hC
  have hEV := CryptoVerification.LibsignalTripleRatchet.Prost.encodeVarint_ok_ext_x img A ext
    (Proofs.libsignal.Hooks2.do_reserve_ok_ext_x hC.alloc)
  have hRaw := Proofs.libsignal.Hooks2.encodeRaw_ok_of_serContractsX hC
  have hDrop := Proofs.libsignal.Hooks2.drop_session_structure_local1_ok_ext hC.alloc
  exact Proofs.libsignal.Hooks2.serializeCanonX_of_serializeX
    (CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX.serialize_ok_of_leaves_ext
      hC hClone hEV hRaw hDrop)

set_option maxRecDepth 2000000 in
theorem serializeStackX_val : Proofs.libsignal.Hooks2.serializeStackX = 155552 := by decide

end CryptoVerification.SignalSession.Cli.Store.SerGlueX

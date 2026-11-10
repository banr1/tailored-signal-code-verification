/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionVtables
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdRegIdVtables
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentitySpec
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionSpec

/-!
# Stage 5 Vtable and File-System Frame Helpers

Layout-independent `.data.rel.ro` vtable dispatch and size/alignment lemmas for
`get_local_registration_id`, `save_identity`, and `store_session`, together with
`subroutine_ok_keepsFiles`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas

open Arm64 ProofLib ProofLib.ProgramReflection ProofLib.ObjectLoad
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

set_option maxRecDepth 200000

/-- Spec wrapper extending `spec.post` with `sf.fs.files = s0.fs.files`. -/
def keepsFiles {α : Type} (spec : Spec α) : Spec α :=
  { spec with post := fun x s0 sf => ⌜sf.fs.files = s0.fs.files⌝ ∗ spec.post x s0 sf }

/-- Under `TraceFsSound prog`, any `subroutine_ok` contract that guarantees `sf.trace = s0.trace`
on normal return automatically preserves `s.fs.files`. -/
theorem subroutine_ok_keepsFiles {α : Type} {prog : Program} {fn : BitVec 64} {spec : Spec α}
    (hFs : TraceFsSound prog) (hok : subroutine_ok prog fn spec)
    (htr : ∀ x s0 sf R, (sf.mem ⊨ spec.post x s0 sf ∗ R) → sf.trace = s0.trace) :
    subroutine_ok prog fn (keepsFiles spec) := by
  have hw := subroutine_ok_withStepsPost hok
  refine subroutine_ok_mono hw (fun _ _ _ h => h) ?_ (fun _ _ _ _ h => h)
    (fun _ _ _ _ _ h => h) (fun _ _ _ _ h => h)
  intro x R s0 sf hpost
  change sf.mem ⊨ (⌜Steps prog s0 sf⌝ ∗ spec.post x s0 sf) ∗ R at hpost
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  obtain ⟨hst, hpost'⟩ := hpost
  have heq : sf.trace = s0.trace := htr x s0 sf R hpost'
  have hfiles : sf.fs.files = s0.fs.files :=
    hFs.files_eq hst (evs := []) (by rw [heq, List.append_nil]) NoFsEv.nil
  change sf.mem ⊨ (⌜sf.fs.files = s0.fs.files⌝ ∗ spec.post x s0 sf) ∗ R
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hfiles, hpost'⟩

/-! ## Raw `.data.rel.ro` Size & Alignment Words -/

theorem rodata_idRegIdFutSize_eq :
    (libsignalSessionImage.data.drop
      (num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}") - 16) -
        libsignalSessionImage.dataOff)).take 8 =
      unpack64 16#64 :=
  KitInst.rodata_cliIdRegIdFutSize_eq

theorem rodata_idRegIdFutAlign_eq :
    (libsignalSessionImage.data.drop
      (num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id::{closure#0}") - 8) -
        libsignalSessionImage.dataOff)).take 8 =
      unpack64 8#64 :=
  KitInst.rodata_cliIdRegIdFutAlign_eq

theorem rodata_idSaveFutSize_eq :
    (libsignalSessionImage.data.drop
      (num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}") - 16) -
        libsignalSessionImage.dataOff)).take 8 =
      unpack64 32#64 :=
  KitInst.rodata_cliIdSaveFutSize_eq

theorem rodata_idSaveFutAlign_eq :
    (libsignalSessionImage.data.drop
      (num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}") - 8) -
        libsignalSessionImage.dataOff)).take 8 =
      unpack64 8#64 :=
  KitInst.rodata_cliIdSaveFutAlign_eq

theorem rodata_sessStoreFutSize_eq :
    (libsignalSessionImage.data.drop
      (num% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}") - 16) -
        libsignalSessionImage.dataOff)).take 8 =
      unpack64 32#64 :=
  KitInst.rodata_cliSessStoreFutSize_eq

theorem rodata_sessStoreFutAlign_eq :
    (libsignalSessionImage.data.drop
      (num% (ls_reloc% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::store_session::{closure#0}") - 8) -
        libsignalSessionImage.dataOff)).take 8 =
      unpack64 8#64 :=
  KitInst.rodata_cliSessStoreFutAlign_eq

/-! ## `fnOff` & Vtable `.data.rel.ro` Intro Lemmas -/

theorem futDrop_fnOff_nat :
    BitVec.ofNat 64 (libsignalSessionCode.fnOff KitInst.cliIdFutDropName) =
      KitInst.cliIdFutDropOff := by
  rw [KitInst.cliIdFutDrop_fnOff]

theorem idVt_eq_cliIdVtOff (img : Obj.Image) :
    idVt img = img.base + KitInst.cliIdVtOff := rfl

theorem sessVt_eq_cliSessVtOff (img : Obj.Image) :
    sessVt img = img.base + KitInst.cliSessVtOff := rfl

private def dummyPeer : AddrGhost :=
  { name := { cap := 0, ptr := 0, bytes := [] }
    device := 1 }

private theorem dummyIdVtablesOk {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img) :
    IdentityVtablesOk img
      (KitInst.cliIdentityStoreSpec E2E.HooksE.A0 img.base cliIo.rd (fun _ => none) (fun _ => True)
        dummyPeer 0 0 0 0) :=
  KitInst.cliIdentityStoreSpec_vtablesOk himg

private theorem dummySessVtablesOk {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img) :
    CryptoVerification.LibsignalPublicApi.MessageDecrypt.SessionOnlyVtablesOk img
      (KitInst.cliSessionStoreSpec E2E.HooksE.A0 img.base cliIo.rd (fun _ => none) (fun _ => True)
        (fun _ => False) dummyPeer 0 0 0 0) :=
  KitInst.cliSessionStoreSpec_vtablesOk himg

theorem idVt_regIdShim_rodata {img : Obj.Image} {s : State} {P : SepProp}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s)
    (hP : s.mem ⊨ P) :
    s.mem ⊨ (((idVt img + 32#64) ↦₆₄ᵣ
      (img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff idRegIdShimName))) ∗ P) := by
  rw [idRegIdShim_fnOff, idVt_eq_cliIdVtOff]
  exact KitInst.cliIdRegIdSlot_ok himg hF hP

theorem idRegIdFut_drop_rodata {img : Obj.Image} {s : State} {P : SepProp}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s)
    (hP : s.mem ⊨ P) :
    s.mem ⊨ (((img.base + idRegIdFutVtOff) ↦₆₄ᵣ
      (img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff KitInst.cliIdFutDropName))) ∗ P) := by
  rw [futDrop_fnOff_nat]
  exact KitInst.cliIdRegIdFutDrop_ok himg hF hP

theorem idRegIdFut_size_rodata {img : Obj.Image} {s : State} {P : SepProp}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s)
    (hP : s.mem ⊨ P) :
    s.mem ⊨ (((img.base + idRegIdFutVtOff + 8#64) ↦₆₄ᵣ 16#64) ∗ P) :=
  KitInst.cliIdRegIdFutSize_ok himg hF hP

theorem idRegIdFut_align_rodata {img : Obj.Image} {s : State} {P : SepProp}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s)
    (hP : s.mem ⊨ P) :
    s.mem ⊨ (((img.base + idRegIdFutVtOff + 16#64) ↦₆₄ᵣ 8#64) ∗ P) :=
  KitInst.cliIdRegIdFutAlign_ok himg hF hP

theorem idRegIdFut_poll_rodata {img : Obj.Image} {s : State} {P : SepProp}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s)
    (hP : s.mem ⊨ P) :
    s.mem ⊨ (((img.base + idRegIdFutVtOff + 24#64) ↦₆₄ᵣ
      (img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff idRegIdPollName))) ∗ P) := by
  rw [idRegIdPoll_fnOff]
  exact KitInst.cliIdRegIdFutPoll_ok himg hF hP

theorem idVt_saveShim_rodata {img : Obj.Image} {s : State} {P : SepProp}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s)
    (hP : s.mem ⊨ P) :
    s.mem ⊨ (((idVt img + 40#64) ↦₆₄ᵣ
      (img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff idSaveShimName))) ∗ P) := by
  rw [idSaveShim_fnOff, idVt_eq_cliIdVtOff]
  exact (dummyIdVtablesOk himg).saveSlot hF hP

theorem idSaveFut_drop_rodata {img : Obj.Image} {s : State} {P : SepProp}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s)
    (hP : s.mem ⊨ P) :
    s.mem ⊨ (((img.base + idSaveFutVtOff) ↦₆₄ᵣ
      (img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff KitInst.cliIdFutDropName))) ∗ P) := by
  rw [futDrop_fnOff_nat]
  exact (dummyIdVtablesOk himg).saveFutDrop hF hP

theorem idSaveFut_size_rodata {img : Obj.Image} {s : State} {P : SepProp}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s)
    (hP : s.mem ⊨ P) :
    s.mem ⊨ (((img.base + idSaveFutVtOff + 8#64) ↦₆₄ᵣ 32#64) ∗ P) :=
  (dummyIdVtablesOk himg).saveFutSize hF hP

theorem idSaveFut_align_rodata {img : Obj.Image} {s : State} {P : SepProp}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s)
    (hP : s.mem ⊨ P) :
    s.mem ⊨ (((img.base + idSaveFutVtOff + 16#64) ↦₆₄ᵣ 8#64) ∗ P) :=
  (dummyIdVtablesOk himg).saveFutAlign hF hP

theorem idSaveFut_poll_rodata {img : Obj.Image} {s : State} {P : SepProp}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s)
    (hP : s.mem ⊨ P) :
    s.mem ⊨ (((img.base + idSaveFutVtOff + 24#64) ↦₆₄ᵣ
      (img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff idSavePollName))) ∗ P) := by
  rw [idSavePoll_fnOff]
  exact (dummyIdVtablesOk himg).saveFutPoll hF hP

theorem sessVt_storeShim_rodata {img : Obj.Image} {s : State} {P : SepProp}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s)
    (hP : s.mem ⊨ P) :
    s.mem ⊨ (((sessVt img + 32#64) ↦₆₄ᵣ
      (img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff sessStoreShimName))) ∗ P) := by
  rw [sessStoreShim_fnOff, sessVt_eq_cliSessVtOff]
  exact (dummySessVtablesOk himg).storeSlot hF hP

theorem sessStoreFut_drop_rodata {img : Obj.Image} {s : State} {P : SepProp}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s)
    (hP : s.mem ⊨ P) :
    s.mem ⊨ (((img.base + sessStoreFutVtOff) ↦₆₄ᵣ
      (img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff KitInst.cliIdFutDropName))) ∗ P) := by
  rw [futDrop_fnOff_nat]
  exact (dummySessVtablesOk himg).storeFutDrop hF hP

theorem sessStoreFut_size_rodata {img : Obj.Image} {s : State} {P : SepProp}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s)
    (hP : s.mem ⊨ P) :
    s.mem ⊨ (((img.base + sessStoreFutVtOff + 8#64) ↦₆₄ᵣ 32#64) ∗ P) :=
  (dummySessVtablesOk himg).storeFutSize hF hP

theorem sessStoreFut_align_rodata {img : Obj.Image} {s : State} {P : SepProp}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s)
    (hP : s.mem ⊨ P) :
    s.mem ⊨ (((img.base + sessStoreFutVtOff + 16#64) ↦₆₄ᵣ 8#64) ∗ P) :=
  (dummySessVtablesOk himg).storeFutAlign hF hP

theorem sessStoreFut_poll_rodata {img : Obj.Image} {s : State} {P : SepProp}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s)
    (hP : s.mem ⊨ P) :
    s.mem ⊨ (((img.base + sessStoreFutVtOff + 24#64) ↦₆₄ᵣ
      (img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff sessStorePollName))) ∗ P) := by
  rw [sessStorePoll_fnOff]
  exact (dummySessVtablesOk himg).storeFutPoll hF hP

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas

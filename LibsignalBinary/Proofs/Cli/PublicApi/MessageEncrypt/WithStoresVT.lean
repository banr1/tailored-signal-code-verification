/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg6
public import LibsignalBinary.Proofs.E2E.Record.Support.Repr
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Assembly
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.SegmentProofs
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg2
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg3
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.Encrypt
import LibsignalBinary.Proofs.Cli.TripleRatchet.Encrypt.Core
import LibsignalBinary.Proofs.Cli.TripleRatchet.SpqrSendEmpty.Core
import LibsignalBinary.Proofs.Cli.TripleRatchet.SpqrSendEmpty.Fetch
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleeProofs.UnackItems
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.Compose
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.SpqrV1Empty
import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpoch
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WP.Apply

/-!
# CLI MessageEncrypt `WithStoresVT`: assembly on `trTrapProgAt` and transfer to `cliExterns`

1. Chains `Seg1..Seg6` (`h45_seg*_okVT_trap`) into `withStores_okVT_fs_trap` (and corollary
   `withStores_okVT_trap`) on `trTrapProgAt img.base C abs`.
2. Proves the empty-SPQR `OtrEncryptOkQ_trap (· = [])` on `trTrapProgAt` (`h45_otrEncryptOkQ_empty_trap`)
   and restricts `kit` to `rem = x.rem.val` (`h45_kitAt`) to discharge the `RecordPqEmpty` arm via
   `withStores_okV_fs_trap` with `TokenInit img` framed.
3. Unifies the `64 ≤ x.rest.length` arm (`withStores_okVT_fs_trap` + `otrEncryptV1_run_trap`) and
   the `RecordPqEmpty` arm (`withStores_okV_fs_trap` + `spqrV1_emptyOk`), then transfers via
   `Slots.subroutine_ok_cli_of_trTrap` to deliver `withStores_okVT_fs_cli` on
   `tripleRatchetProgAtExt img.base (cliExterns W)`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalTripleRatchet.SpqrSendEmpty

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet

section SpqrSendEmptyTrap

attribute [local irreducible] Program.fetch Program.externAt?

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

set_option maxRecDepth 200000 in
set_option maxHeartbeats 1200000 in
theorem h45_spqrSendEmpty_base_ext_trap (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (img : Obj.Image) (hC : Stage2Contracts_trap img.base C A uuidTryParse S ext) (hE : S.SendEmptyOk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendName)
      (CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendEmptySpec A ctl S img) := by
  have hfn := (ls_lemma% fnOff "spqr::send::<libsignal_cli_ratchet::Coins>")
  have hdec := sub_ok_at_of_fnAddr hC.decode_state_empty decodeStateName 0 (Nat.add_zero _)
  rw [← CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendEmpty.spqrSend_add_decodeState_eq_fnAddr] at hdec
  have hmc := memcpyPcs_of_sessionMemcpyRegion
    (hC.session_memcpy_region_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendName
      (num% (ls_off% "memcpy" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>")))
  spqr_fetches_cli img.base (Rust.withPanics ext) hfn 0 108
  spqr_fetches_cli img.base (Rust.withPanics ext) hfn 136 88
  spqr_fetches_cli img.base (Rust.withPanics ext) hfn 4608 12
  spqr_fetches_cli img.base (Rust.withPanics ext) hfn 4632 36
  simp only [CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendEmptySpec,
    CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendSpec, Spec.inImage, stackAt_spqr]
  simp (config := { maxSteps := 1000000 }) only [sepExists_sepConj_left, sepExists_sepConj_right]
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨ret, ⟨v, cap, ptr, bs⟩, cur, rest⟩ := x
  dsimp only at *
  subst bs
  wp_steps
  wp_apply
  wp_simp_pre only [decodeEmpty_split, sepExists_sepConj_left, sepExists_sepConj_right,
    sepConj_assoc]
  apply SepWP.exists_elim; intro d3
  apply SepWP.exists_elim; intro d2
  apply SepWP.exists_elim; intro d1
  wp_steps
  wp_apply
  wp_simp_pre only [ret_split ret, sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro r6
  apply SepWP.exists_elim; intro r5
  apply SepWP.exists_elim; intro r4
  apply SepWP.exists_elim; intro r3
  apply SepWP.exists_elim; intro r2
  apply SepWP.exists_elim; intro r1
  apply SepWP.exists_elim; intro r0
  wp_steps
  refine SepWP.fold (dst_fold s0.sp pqChainNone pqInnerNone) (by sep_focus) ?_
  refine SepWP.fold (decode_fold s0.sp 0xFFFFFFFFFFFFFFFF#64 d1 d2 d3 pqChainNone pqInnerNone)
    (by sep_focus) ?_
  refine SepWP.fold (result_fold A ret) (by sep_focus) ?_
  refine SepWP.fold (CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendEmpty.tape_fold img.base cur rest)
    (by sep_focus) ?_
  simp only [hE.send, hE.draws, hE.noPanic]
  wp_done

theorem h45_spqrSendEmpty_base_trap (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (img : Obj.Image) (hHooks : TripleRatchetHooks C A S abs) (hE : S.SendEmptyOk) :
    subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendName)
      (CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendEmptySpec A ctl S img) :=
  h45_spqrSendEmpty_base_ext_trap C A ctl S (trTrapExterns C abs) img
    (Stage2Contracts_trap.of_tripleRatchetProgAt_trap img.base C A S abs hHooks) hE

end SpqrSendEmptyTrap

end CryptoVerification.LibsignalTripleRatchet.SpqrSendEmpty

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (SessionOnlyKitOkSE SessionOnlyVtablesOk)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreKitOkIE)
open CryptoVerification.LibsignalSpqrV1 (TokenInit spqrV1 spqrV1_emptyOk)
open CryptoVerification.SignalSession (CliHooks cliExterns)
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Slots

attribute [local irreducible] Program.fetch Program.externAt?

/-! ## 1. Segment Chaining & `withStores_okVT_fs_trap` -/

private theorem h45_segExitVT_chain_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {x : WithStoresEncGhost} {R : SepProp}
    {s0 s : State} {next : State → Prop}
    (h1 : h45_SegExitVT_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s next)
    (h2 : ∀ s', next s' → reaches_outcome (trTrapProgAt img.base C abs)
      (withStoresEncSpecVT_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord) x R s0 s') :
    reaches_outcome (trTrapProgAt img.base C abs)
      (withStoresEncSpecVT_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord) x R s0 s := by
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact reaches_outcome_steps hst (h2 sf hnext)
  · exact reaches_outcome_steps hst (reaches_outcome.of_outcome hout)

private theorem h45_segExitVT_chainFs_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {x : WithStoresEncGhost} {R : SepProp}
    {s0 s : State} {next : State → Prop}
    (hfs : EncFsCtx_trap kit ikit C abs s0 s)
    (h1 : h45_SegExitVT_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s next)
    (h2 : ∀ s', EncFsCtx_trap kit ikit C abs s0 s' → next s' →
      reaches_outcome (trTrapProgAt img.base C abs)
        (withStoresEncSpecVT_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord) x R s0 s') :
    reaches_outcome (trTrapProgAt img.base C abs)
      (withStoresEncSpecVT_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord) x R s0 s := by
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact reaches_outcome_steps hst (h2 sf (hfs.of_steps hst) hnext)
  · exact reaches_outcome_steps hst (reaches_outcome.of_outcome hout)

/-- Frame-generalised `withStores_okV_fs_trap` with `64 ≤ x.rest.length` and `TokenInit img`
framed, carrying both kits' `envOk` from `KitFsOk`. -/
theorem withStores_okVT_fs_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hEnv : EncEnvT_trap kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord abs)
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (trTrapProgAt img.base C abs)) :
    subroutine_ok (trTrapProgAt img.base C abs) (encEntry img)
      (withEnvPre (withStoresEncSpecVT_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre0 hal => ?_
  obtain ⟨h0, hpre⟩ := withEnvPre_pre_elim hpre0
  rw [reaches_outcome_withEnvPre]
  have hpre_rearr : s0.mem ⊨ ⌜64 ≤ x.rest.length⌝ ∗
      ((withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).pre x s0 ∗
        (TokenInit img ∗ R)) := by
    change s0.mem ⊨ (⌜64 ≤ x.rest.length⌝ ∗ TokenInit img ∗
      (withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).pre x s0) ∗ R at hpre
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre_rearr
  rcases hpre_rearr with ⟨h64, hpreV⟩
  have ⟨haddr_ss, haddr_id⟩ := withStoresEncSpecV_pre_addrOk hpreV
  have hfs0 : EncFsCtx_trap kit ikit C abs s0 s0 := FsCtx.of_entry hKitFs h0
  refine h45_segExitVT_chainFs_trap hfs0
    (h45_segExitVT_of_segExit_trap
      (h45_segLoad_okVT_trap hEnv x (TokenInit img ∗ R) s0 hfs0 hpc hrun hal hpreV)) ?_
  rintro s hfs ⟨r, g, sess, hCur⟩
  refine h45_segExitVT_chainFs_trap hfs
    (h45_segExitVT_of_segExit_trap
      (h45_segFrom_okVT_trap hEnv x r g sess (TokenInit img ∗ R) s0 s hCur)) ?_
  rintro s hfs ⟨otr, taken, pqCap, pqPtr, hOtr⟩
  refine h45_segExitVT_chainFs_trap hfs
    (h45_segExitVT_of_segExit_trap
      (h45_segIdentity_okVT_trap hEnv x r sess otr taken pqCap pqPtr (TokenInit img ∗ R) s0 s hOtr)) ?_
  rintro s hfs ⟨k, hKey⟩
  have hCm : h45_SegExitVT_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s
      (fun s' => ∃ m otr' pqCap' pqPtr',
        CmStateV kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord x r sess otr taken k m otr' pqCap'
          pqPtr' (TokenInit img ∗ R) s0 s') := by
    cases hp : sess.pendingPreKey with
    | none => exact h45_segSignal_okVT_trap hEnv x r sess otr taken pqCap pqPtr k R s0 s h64 hp hKey
    | some _ =>
      exact h45_segPreKey_okVT_trap hEnv x r sess otr taken pqCap pqPtr k R s0 s h64 (by simp [hp]) hKey
  refine h45_segExitVT_chainFs_trap hfs hCm ?_
  rintro s hfs ⟨m, otr', pqCap', pqPtr', hCmS⟩
  refine h45_segExitVT_chainFs_trap hfs
    (h45_segExitVT_of_segExit_trap
      (h45_segTrust_okVT_trap hEnv x r sess otr taken k m otr' pqCap' pqPtr' (TokenInit img ∗ R) s0 s haddr_id hfs hCmS)) ?_
  intro s hfs hSave
  refine h45_segExitVT_chainFs_trap hfs
    (h45_segExitVT_of_segExit_trap
      (h45_segSave_okVT_trap hEnv x r sess otr taken k m otr' pqCap' pqPtr' (TokenInit img ∗ R) s0 s haddr_id hfs hSave)) ?_
  rintro s hfs ⟨c, hApply⟩
  refine h45_segExitVT_chainFs_trap hfs
    (h45_segExitVT_of_segExit_trap
      (h45_segApplyStore_okVT_trap hEnv x r sess otr taken k m otr' pqCap' pqPtr' c (TokenInit img ∗ R) s0 s haddr_ss hfs hApply)) ?_
  intro s _ hStored
  exact h45_segExitVT_chain_trap
    (h45_segExitVT_of_segExit_trap
      (h45_segFinish_okVT_trap hEnv x r sess otr taken k m otr' c (TokenInit img ∗ R) s0 s hStored))
    (fun _ hF => False.elim hF)

/-- Corollary of `withStores_okVT_fs_trap` when `envOk` holds trivially. -/
theorem withStores_okVT_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hEnv : EncEnvT_trap kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord abs)
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (trTrapProgAt img.base C abs) (encEntry img)
      (withStoresEncSpecVT_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord) :=
  subroutine_ok_of_withEnvPre (withStores_okVT_fs_trap hEnv (.inl htriv)) fun s => htriv s.fs.files

/-! ## 2. Empty-SPQR `OtrEncryptOkQ_trap (· = [])` on `trTrapProgAt` -/

private theorem h45_otrEncryptOkQ_empty_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {abs : String → Option (State → State)}
    (hHooks : TripleRatchetHooks C A S abs)
    (hE : S.SendEmptyOk)
    (himg : Obj.Loads libsignalSessionImage img) :
    OtrEncryptOkQ_trap (· = []) img C A ctl uuidTryParse S abs := by
  obtain ⟨hMK, hGK, hNew, hNCK⟩ :=
    CryptoVerification.Cli.LibsignalSpqrV1.M4.encryptCallees_trap C A S abs img hHooks himg
  exact CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt.otrEncrypt_body_ok_trap
    (· = []) C A ctl S abs img hHooks himg
    (CryptoVerification.LibsignalTripleRatchet.SpqrSendEmpty.h45_spqrSendEmpty_base_trap
      C A ctl S abs img hHooks hE) hMK hGK hNew hNCK

/-! ## 3. Remote-Address Kit Restriction (`h45_kitAt`) for the `RecordPqEmpty` Arm -/

@[reducible] private def h45_kitAt {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (target : AddrVal) : SessionStoreSpec A b :=
  { kit with
    addrOk := fun rem => kit.addrOk rem ∧ rem = target
    loadRel := fun st rem ans => kit.loadRel st rem ans ∧ rem = target }

private theorem h45_pure_mono {φ ψ : Prop} (h : φ → ψ) : (⌜φ⌝ : SepProp) ⊢ ⌜ψ⌝ :=
  Entails.pure_left_only fun hφ => Entails.pure_right_only (h hφ) (Entails.refl _)

private theorem h45_storeFinal_kitAt {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (target : AddrVal) (st0 : kit.StoreState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    (h45_kitAt kit target).storeFinal st0 ans calls = kit.storeFinal st0 ans calls := by
  induction calls generalizing st0 with
  | nil => rfl
  | cons c cs ih => cases c <;> simp only [SessionStoreSpec.storeFinal, h45_kitAt, ih]

private theorem h45_traceOfWith_kitAt {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (target : AddrVal) (ikit : IdentityStoreSpec A b)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ans : StoreAnswers (List (BitVec 8)) Unit) (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    ikit.traceOfWith (h45_kitAt kit target) encRecord ans calls =
      ikit.traceOfWith kit encRecord ans calls :=
  rfl

private theorem h45_stackV_kitAt {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (target : AddrVal) (ikit : IdentityStoreSpec A b) :
    withStoresEncStackV (h45_kitAt kit target) ikit = withStoresEncStackV kit ikit :=
  rfl

private theorem h45_callsRel_kitAt_imp {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (target : AddrVal) (st0 : kit.StoreState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    (h45_kitAt kit target).callsRel st0 ans calls → kit.callsRel st0 ans calls := by
  induction calls generalizing st0 with
  | nil => exact id
  | cons c cs ih =>
    cases c with
    | loadSession rem =>
      intro ⟨⟨hl, _⟩, hcs⟩
      exact ⟨hl, ih st0 hcs⟩
    | isTrustedIdentity _ _ _ =>
      intro hcs
      exact ih st0 hcs
    | saveIdentity _ _ =>
      intro hcs
      exact ih st0 hcs
    | storeSession rem r' =>
      intro ⟨hs, hcs⟩
      exact ⟨hs, ih st0 hcs⟩

private theorem h45_stepsThroughEncrypt_mono {Scope1 Scope2 : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {S : SpqrModel} {parse : UuidParser} {x : WithStoresEncGhost}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {otr : OutgoingTripleRatchet (List (BitVec 8))} {taken : SessionState (List (BitVec 8))}
    {k : IdentityKey} {m : CiphertextMessage} {otr' : OutgoingTripleRatchet (List (BitVec 8))}
    (himp : ∀ r', Scope1 r' → Scope2 r')
    (h : StepsThroughEncrypt Scope1 C S parse x r sess otr taken k m otr') :
    StepsThroughEncrypt Scope2 C S parse x r sess otr taken k m otr' :=
  ⟨h.1, himp r h.2.1, h.2.2⟩

private theorem h45_sessionOnlyKitOkSE_kitAt {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {ext : String → Option (State → State)}
    (target : AddrVal)
    (hKitOk : SessionOnlyKitOkSE kit Scope encRecord ext) :
    SessionOnlyKitOkSE (h45_kitAt kit target) Scope encRecord ext where
  loadShim := hKitOk.loadShim
  loadFutDrop := hKitOk.loadFutDrop
  storeShim := hKitOk.storeShim
  storeFutDrop := hKitOk.storeFutDrop
  loadPoll := by
    refine subroutine_ok_outcome_intro fun ⟨c, self, st⟩ R s0 hpc hrun hpre0 hal => ?_
    obtain ⟨henv, hpre⟩ := withEnvPre_pre_elim hpre0
    rw [reaches_outcome_withEnvPre]
    have hpre_pure : s0.mem ⊨
        ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab ∧
          s0.readReg64 .x0 = c.fut ∧ s0.readReg64 .x8 = c.out ∧
          (kit.addrOk c.addr.val ∧ c.addr.val = target)⌝ ∗
        (kit.loadBoxAt c.fut self c.addrA 0#8 ∗ kit.storeAt self st ∗ memRegion c.out 368 ∗
          protocolAddressAt A c.addr c.addrA ∗ A.pool ∗ stackAt s0.sp kit.loadPollStack ∗ R) := by
      simpa only [kitLoadPollSpecS, h45_kitAt, sepConj_assoc] using hpre
    rw [satisfies_pure_sepConj] at hpre_pure
    rcases hpre_pure with ⟨⟨hfroz, hsym, hx0, hx8, haddr, hrem⟩, hmem⟩
    have hpre_kit : s0.mem ⊨
        (kitLoadPollSpecS img kit Scope encRecord).pre (c, self, st) s0 ∗ R := by
      dsimp only [kitLoadPollSpecS]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hfroz, hsym, hx0, hx8, haddr⟩, by simpa only [sepConj_assoc] using hmem⟩
    have hcall := hKitOk.loadPoll.to_outcome (c, self, st) R s0 hpc hrun (withEnvPre_pre_intro henv hpre_kit) hal
    rw [reaches_outcome_withEnvPre] at hcall
    refine hcall.mono_outcome (fun sf hout => ?_)
    rcases hout with ⟨hret, hcs, hpost⟩ | hpan | hexit | hoom
    · refine Or.inl ⟨hret, hcs, ?_⟩
      dsimp only [kitLoadPollSpecS, h45_kitAt] at hpost ⊢
      refine Satisfies.mono (sepConj_mono_left (Entails.sepExists_elim fun ans =>
        Entails.sepExists_right ans ?_)) hpost
      exact sepConj_mono_left (h45_pure_mono fun ⟨hl, htr⟩ => ⟨⟨hl, hrem⟩, htr⟩)
    · exact Or.inr (Or.inl hpan)
    · exact Or.inr (Or.inr (Or.inl hexit))
    · exact Or.inr (Or.inr (Or.inr hoom))
  storePoll := by
    refine subroutine_ok_outcome_intro fun ⟨c, self, st⟩ R s0 hpc hrun hpre0 hal => ?_
    dsimp only [Spec.inImage] at hpre0
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
    rcases hpre0 with ⟨himg_s0, hpre1⟩
    obtain ⟨henv, hpre⟩ := withEnvPre_pre_elim hpre1
    have hpre_pure : s0.mem ⊨
        ⌜s0.readReg64 .x0 = c.fut ∧ s0.readReg64 .x8 = c.out ∧ kit.RecOk c.call.record ∧
          (kit.addrOk c.call.addr.val ∧ c.call.addr.val = target)⌝ ∗
        (kit.storeBoxAt c.fut self c.call.addrA c.call.recA 0#8 ∗
          kit.storeAt self st ∗ memRegion c.out 48 ∗
          protocolAddressAt A c.call.addr c.call.addrA ∗
          sessionRecordAt A c.call.recA c.call.g c.call.record ∗
          A.pool ∗ stackAt s0.sp kit.storePollStack ∗ R) := by
      simpa only [kitStorePollSpec, h45_kitAt, sepConj_assoc] using hpre
    rw [satisfies_pure_sepConj] at hpre_pure
    rcases hpre_pure with ⟨⟨hx0, hx8, hrec, haddr, _⟩, hmem⟩
    have hpre_kit : s0.mem ⊨
        ((kitStorePollSpecE kit encRecord).inImage img).pre (c, self, st) s0 ∗ R := by
      dsimp only [Spec.inImage]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨himg_s0, withEnvPre_pre_intro henv ?_⟩
      dsimp only [kitStorePollSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx8, hrec, haddr⟩, by simpa only [sepConj_assoc] using hmem⟩
    exact hKitOk.storePoll.mono_outcome (c, self, st) R s0 hpc hrun hpre_kit hal fun _ hout => hout

/-! ## 4. Disjunctive CLI Spec & Exported Theorem (`withStores_okVT_fs_cli`) -/

def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecVT_cli
    {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) : Spec WithStoresEncGhost :=
  { CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV
      kit st0 ikit ist0 C ctl uuidParse S encRecord with
    pre := fun x s =>
      ⌜64 ≤ x.rest.length ∨ (∀ r, kit.ScopeAt Scope st0 x.rem.val r → E2E.Record.RecordPqEmpty r)⌝ ∗
        CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
        (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV
          kit st0 ikit ist0 C ctl uuidParse S encRecord).pre x s
    post := fun x s0 sf =>
      CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
        (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV
          kit st0 ikit ist0 C ctl uuidParse S encRecord).post x s0 sf }

private theorem h45_callees_empty_cli {img : Obj.Image} (W : CliHooks) (ctl : BitVec 64)
    (himg : Obj.Loads libsignalSessionImage img) :
    EncCallees_trap (· = []) img W.C E2E.HooksE.A0 ctl uuidTryParse (spqrV1 W.C.F W.Q.K)
      (cliExterns W) := by
  have hEncHooks := cliEncHooks_of_runHooks W (spqrV1 W.C.F W.Q.K)
  have hTrHooks := cliExterns_tripleRatchetHooks W (spqrV1 W.C.F W.Q.K)
  have hTimeAdd : HookSat (trTrapExterns W.C (cliExterns W)) timeAddHookName timeAddSpec :=
    hEncHooks.timeAdd
  have hUnack : UnackItemsOk_trap img W.C E2E.HooksE.A0 (cliExterns W) :=
    CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.UnackItems.unackItems_ok_trap
      hTimeAdd himg
  have hPsm : PreKeyMsgNewOk_trap img W.C E2E.HooksE.A0 (cliExterns W) :=
    CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Compose.preKeyMsgNew_ok_trap
      hEncHooks.toTripleRatchetHooks himg
  have hOtrEmpty : OtrEncryptOkQ_trap (· = []) img W.C E2E.HooksE.A0 ctl uuidTryParse
      (spqrV1 W.C.F W.Q.K) (cliExterns W) :=
    h45_otrEncryptOkQ_empty_trap hTrHooks (spqrV1_emptyOk W.C.F W.Q.K) himg
  exact encCallees_ok_of_callees_trap hEncHooks hOtrEmpty hUnack hPsm himg

private theorem h45_calleesT_cli {img : Obj.Image} (W : CliHooks) (ctl : BitVec 64)
    (himg : Obj.Loads libsignalSessionImage img) :
    EncCalleesT_trap img W.C E2E.HooksE.A0 ctl uuidTryParse (spqrV1 W.C.F W.Q.K)
      (cliExterns W) := by
  have hc := h45_callees_empty_cli W ctl himg
  have hOtrT : OtrEncryptOkT_trap img W.C E2E.HooksE.A0 ctl uuidTryParse
      (spqrV1 W.C.F W.Q.K) (cliExterns W) :=
    CryptoVerification.Cli.LibsignalSpqrV1.M4.otrEncryptV1_run_trap
      W.C E2E.HooksE.A0 ctl W.Q.K (cliExterns W) img
      (cliExterns_tripleRatchetHooks W (spqrV1 W.C.F W.Q.K))
      (cliExterns_spqrHooks W) himg
  exact ⟨hc.otrFrom, hc.otrApply, hc.remoteIk, hOtrT, hc.unack, hc.kyber, hc.psmNew,
    hc.cmDrop, hc.dropSs⟩

private theorem h45_subroutineOutcome_cli_of_kitAt {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64} {uuidParse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {R : SepProp} {s0 sf : State}
    (h : SubroutineOutcome
      (withStoresEncSpecV (h45_kitAt kit x.rem.val) st0 ikit ist0 C ctl uuidParse S encRecord)
      x (TokenInit img ∗ R) s0 sf) :
    SubroutineOutcome
      (withStoresEncSpecVT_cli kit st0 ikit ist0 Scope C ctl uuidParse S encRecord)
      x R s0 sf := by
  rcases h with ⟨h1, hcs, hpost⟩ | ⟨hpan, honp⟩ | ⟨code, hexit, honex⟩ | ⟨_hoom, honoom⟩
  · refine Or.inl ⟨h1, hcs, ?_⟩
    dsimp only [withStoresEncSpecVT_cli]
    have hrearr : (TokenInit img ∗
        (withStoresEncSpecV kit st0 ikit ist0 C ctl uuidParse S encRecord).post x s0 sf) ∗ R =
      (withStoresEncSpecV kit st0 ikit ist0 C ctl uuidParse S encRecord).post x s0 sf ∗
        (TokenInit img ∗ R) := by ac_rfl
    rw [hrearr]
    refine Satisfies.mono (sepConj_mono_left ?_) hpost
    dsimp only [withStoresEncSpecV, Spec.inImage]
    refine Entails.sepExists_elim fun answers => Entails.sepExists_right answers ?_
    rw [h45_traceOfWith_kitAt kit x.rem.val, h45_storeFinal_kitAt kit x.rem.val,
      h45_stackV_kitAt kit x.rem.val]
    exact sepConj_mono_left (h45_pure_mono fun ⟨hnp, hcalls, hid, htr⟩ =>
      ⟨hnp, h45_callsRel_kitAt_imp kit x.rem.val st0 answers _ hcalls, hid, htr⟩)
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [withStoresEncSpecVT_cli, withStoresEncSpecV, Spec.inImage, h45_kitAt] at honp ⊢
    have hmono1 :
        ⌜s0.trace <+: sf.trace ∧
          (allocFailedIn s0 sf ∨
            ∃ answers : StoreAnswers (List (BitVec 8)) Unit,
              (kit.loadRel st0 x.rem.val answers.loadSession ∧ x.rem.val = x.rem.val) ∧
              s0.trace ++ kit.loadEvs encRecord x.rem.val answers.loadSession <+: sf.trace ∧
              ((x.model C S uuidParse answers).1 = .error .panic ∨ x.sendPanics S answers))⌝ ⊢
        ⌜s0.trace <+: sf.trace ∧
          (allocFailedIn s0 sf ∨
            ∃ answers : StoreAnswers (List (BitVec 8)) Unit,
              kit.loadRel st0 x.rem.val answers.loadSession ∧
              s0.trace ++ kit.loadEvs encRecord x.rem.val answers.loadSession <+: sf.trace ∧
              ((x.model C S uuidParse answers).1 = .error .panic ∨ x.sendPanics S answers))⌝ := by
      refine h45_pure_mono fun ⟨htr, hor⟩ => ⟨htr, ?_⟩
      rcases hor with halloc | ⟨ans, ⟨hl, _⟩, hpfx, herr⟩
      · exact Or.inl halloc
      · exact Or.inr ⟨ans, hl, hpfx, herr⟩
    refine Satisfies.mono ?_ honp
    rw [← sepConj_assoc, sepConj_assoc _ anyHeap (TokenInit img)]
    exact sepConj_mono_left (sepConj_mono hmono1 (entails_anyHeap (anyHeap ∗ TokenInit img)))
  · refine Or.inr (Or.inr (Or.inl ⟨code, hexit, ?_⟩))
    change sf.mem ⊨ ⌜False⌝ ∗ (TokenInit img ∗ R) at honex
    rw [satisfies_pure_sepConj] at honex
    exact False.elim honex.1
  · change sf.mem ⊨ ⌜False⌝ ∗ (TokenInit img ∗ R) at honoom
    rw [satisfies_pure_sepConj] at honoom
    exact False.elim honoom.1

private theorem withStores_okVT_fs_cli_trTrap
    {img : Obj.Image} (W : CliHooks)
    {kit : SessionStoreSpec E2E.HooksE.A0 img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec E2E.HooksE.A0 img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    (ctl : BitVec 64)
    (himg : Obj.Loads libsignalSessionImage img)
    (hKitOk : SessionOnlyKitOkSE kit Scope encRecord (trTrapExterns W.C (cliExterns W)))
    (hIkitOk : IdentityStoreKitOkIE img ikit (trTrapExterns W.C (cliExterns W)))
    (hVtables : SessionOnlyVtablesOk img kit)
    (hIdVtables : IdentityVtablesOk img ikit)
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (trTrapProgAt img.base W.C (cliExterns W)))
    (hScopeIn : ∀ {rem : AddrVal} (r : SessionRecord (List (BitVec 8))),
      kit.ScopeAt Scope st0 rem r → RecordInScopeEnc r)
    (hScopeQ : ∀ {rem : AddrVal} (r : SessionRecord (List (BitVec 8))) (s : Session (List (BitVec 8))),
      kit.ScopeAt Scope st0 rem r → r.currentSession = some s → s.state.pqRatchetState.length < 2 ^ 32)
    (hRecOk : ∀ {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
      {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
      {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {m : CiphertextMessage}
      {otr' : OutgoingTripleRatchet (List (BitVec 8))},
      kit.addrOk x.rem.val →
      StepsThroughEncrypt (kit.ScopeAt Scope st0 x.rem.val) W.C
        (spqrV1 W.C.F W.Q.K) uuidTryParse
        x r sess otr taken k m otr' →
      kit.RecOk (storedRecord sess otr' taken)) :
    subroutine_ok (trTrapProgAt img.base W.C (cliExterns W)) (encEntry img)
      (withEnvPre
        (withStoresEncSpecVT_cli kit st0 ikit ist0 Scope W.C ctl uuidTryParse
          (spqrV1 W.C.F W.Q.K) encRecord)
        (fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre0 hal => ?_
  obtain ⟨h0, hpre⟩ := withEnvPre_pre_elim hpre0
  rw [reaches_outcome_withEnvPre]
  set S := spqrV1 W.C.F W.Q.K
  have hpre_disj : s0.mem ⊨
      ⌜64 ≤ x.rest.length ∨ (∀ r, kit.ScopeAt Scope st0 x.rem.val r → E2E.Record.RecordPqEmpty r)⌝ ∗
      ((TokenInit img ∗
        (withStoresEncSpecV kit st0 ikit ist0 W.C ctl uuidTryParse S encRecord).pre x s0) ∗ R) := by
    change s0.mem ⊨
      (⌜64 ≤ x.rest.length ∨ (∀ r, kit.ScopeAt Scope st0 x.rem.val r → E2E.Record.RecordPqEmpty r)⌝ ∗
        TokenInit img ∗
        (withStoresEncSpecV kit st0 ikit ist0 W.C ctl uuidTryParse S encRecord).pre x s0) ∗ R at hpre
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre_disj
  rcases hpre_disj with ⟨h64 | hpqE, hpre_tok⟩
  · -- Arm 1: `64 ≤ x.rest.length` via `withStores_okVT_fs_trap`
    have hEnvT : EncEnvT_trap kit st0 ikit ist0 Scope W.C ctl uuidTryParse S encRecord
        (cliExterns W) := {
      loads := himg
      hooks := cliEncHooks_of_runHooks W S
      kitOk := hKitOk
      ikitOk := hIkitOk
      callees := h45_calleesT_cli W ctl himg
      vtables := hVtables
      idVtables := hIdVtables
      scopeIn := hScopeIn
      scopeQ := hScopeQ
      recOk := hRecOk
    }
    have hpreVT : s0.mem ⊨
        (withStoresEncSpecVT_trap kit st0 ikit ist0 W.C ctl uuidTryParse S encRecord).pre x s0 ∗ R := by
      dsimp only [withStoresEncSpecVT_trap]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨h64, by simpa only [sepConj_assoc] using hpre_tok⟩
    have hcall := (withStores_okVT_fs_trap hEnvT hKitFs).to_outcome x R s0 hpc hrun
      (withEnvPre_pre_intro h0 hpreVT) hal
    rw [reaches_outcome_withEnvPre] at hcall
    exact hcall.mono_outcome (fun _ hout => hout)
  · -- Arm 2: `RecordPqEmpty` on loaded records for `x.rem.val` via `withStores_okV_fs_trap`
    let kit' := h45_kitAt kit x.rem.val
    have hEnvE : EncEnv_trap kit' st0 ikit ist0 Scope (· = []) W.C ctl uuidTryParse S encRecord
        (cliExterns W) := {
      loads := himg
      hooks := cliEncHooks_of_runHooks W S
      kitOk := h45_sessionOnlyKitOkSE_kitAt x.rem.val hKitOk
      ikitOk := hIkitOk
      callees := h45_callees_empty_cli W ctl himg
      vtables := ⟨hVtables.loadSlot, hVtables.storeSlot, hVtables.loadFutDrop, hVtables.loadFutSize,
        hVtables.loadFutAlign, hVtables.loadFutPoll, hVtables.storeFutDrop, hVtables.storeFutSize,
        hVtables.storeFutAlign, hVtables.storeFutPoll⟩
      idVtables := hIdVtables
      scopeIn := fun r ⟨hsc, hl, _⟩ => hScopeIn r ⟨hsc, hl⟩
      scopeQ := fun r s ⟨hsc, hl, hrem⟩ hsess => by
        subst hrem
        exact hpqE r ⟨hsc, hl⟩ s hsess
      recOk := fun {y r sess otr taken k m otr'} haddr' h15 =>
        hRecOk haddr'.1
          (h45_stepsThroughEncrypt_mono (fun _ ⟨hsc, hl, _⟩ => ⟨hsc, hl⟩) h15)
    }
    have hpreV_rearr : s0.mem ⊨
        (withStoresEncSpecV kit st0 ikit ist0 W.C ctl uuidTryParse S encRecord).pre x s0 ∗
        (TokenInit img ∗ R) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre_tok
    have hpreV' : s0.mem ⊨
        (withStoresEncSpecV kit' st0 ikit ist0 W.C ctl uuidTryParse S encRecord).pre x s0 ∗
        (TokenInit img ∗ R) := by
      refine Satisfies.mono (sepConj_mono_left ?_) hpreV_rearr
      dsimp only [withStoresEncSpecV, Spec.inImage, kit']
      rw [h45_stackV_kitAt kit x.rem.val]
      exact sepConj_mono_right (sepConj_mono_left
        (h45_pure_mono fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hss, hid⟩ =>
          ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, ⟨hss, rfl⟩, hid⟩))
    have hcall := (withStores_okV_fs_trap hEnvE hKitFs).to_outcome x (TokenInit img ∗ R) s0 hpc hrun
      (withEnvPre_pre_intro h0 hpreV') hal
    rw [reaches_outcome_withEnvPre] at hcall
    exact hcall.mono_outcome (fun _ hout => h45_subroutineOutcome_cli_of_kitAt hout)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStores_okVT_fs_cli
    {img : Obj.Image} (W : CliHooks)
    {kit : SessionStoreSpec E2E.HooksE.A0 img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec E2E.HooksE.A0 img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    (ctl : BitVec 64)
    (himg : Obj.Loads libsignalSessionImage img)
    (hKitOk : CryptoVerification.LibsignalPublicApi.MessageDecrypt.SessionOnlyKitOkSE
      kit Scope encRecord (trTrapExterns W.C (cliExterns W)))
    (hIkitOk : CryptoVerification.LibsignalPublicApi.StoreKit.Identity.IdentityStoreKitOkIE
      img ikit (trTrapExterns W.C (cliExterns W)))
    (hVtables : CryptoVerification.LibsignalPublicApi.MessageDecrypt.SessionOnlyVtablesOk img kit)
    (hIdVtables : IdentityVtablesOk img ikit)
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (trTrapProgAt img.base W.C (cliExterns W)))
    (hScopeIn : ∀ {rem : AddrVal} (r : SessionRecord (List (BitVec 8))),
      kit.ScopeAt Scope st0 rem r → RecordInScopeEnc r)
    (hScopeQ : ∀ {rem : AddrVal} (r : SessionRecord (List (BitVec 8))) (s : Session (List (BitVec 8))),
      kit.ScopeAt Scope st0 rem r → r.currentSession = some s → s.state.pqRatchetState.length < 2 ^ 32)
    (hRecOk : ∀ {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
      {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
      {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {m : CiphertextMessage}
      {otr' : OutgoingTripleRatchet (List (BitVec 8))},
      kit.addrOk x.rem.val →
      StepsThroughEncrypt (kit.ScopeAt Scope st0 x.rem.val) W.C
        (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K) uuidTryParse
        x r sess otr taken k m otr' →
      kit.RecOk (storedRecord sess otr' taken)) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr "libsignal_cli_ratchet::encrypt")
      (withEnvPre
        (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecVT_cli
          kit st0 ikit ist0 Scope W.C ctl uuidTryParse
          (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K) encRecord)
        (fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files)) := by
  have htrap := withStores_okVT_fs_cli_trTrap (ist0 := ist0) W ctl himg hKitOk hIkitOk
    hVtables hIdVtables hKitFs hScopeIn hScopeQ hRecOk
  dsimp only [encEntry, CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName] at htrap
  rw [entryOf_eq_trTrapProgAt W.C (cliExterns W) himg "libsignal_cli_ratchet::encrypt"] at htrap
  exact subroutine_ok_cli_of_trTrap htrap

end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt

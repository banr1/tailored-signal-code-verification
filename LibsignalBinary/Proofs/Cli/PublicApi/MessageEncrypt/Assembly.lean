/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Segs
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.SegmentProofs

/-!
# CLI `MessageEncrypt` Assembly

Composes the nine `MessageEncrypt` segment specifications into `withStores_okV_trap` and
`withStores_okV_fs_trap` on `trTrapProgAt`, with CLI entry-point corollaries on
`tripleRatchetProgAtExt img.base (cliExterns W)`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit

variable {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
  {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
  {abs : String → Option (State → State)}

/-- Chain a segment exit into the remainder of the run (`next` continues; outcome exits finish). -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segExit_chain_trap {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {x : WithStoresEncGhost} {R : SepProp}
    {s0 s : State} {next : State → Prop}
    (h1 : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s next)
    (h2 : ∀ s', next s' → reaches_outcome (trTrapProgAt img.base C abs)
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord) x R s0 s') :
    reaches_outcome (trTrapProgAt img.base C abs)
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord) x R s0 s := by
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact reaches_outcome_steps hst (h2 sf hnext)
  · exact reaches_outcome_steps hst (reaches_outcome.of_outcome hout)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segExit_chain {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {x : WithStoresEncGhost} {R : SepProp}
    {s0 s : State} {next : State → Prop}
    (h1 : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s next)
    (h2 : ∀ s', next s' → reaches_outcome (tripleRatchetProgAt img.base C ctl abs)
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord) x R s0 s') :
    reaches_outcome (tripleRatchetProgAt img.base C ctl abs)
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord) x R s0 s := by
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact reaches_outcome_steps hst (h2 sf hnext)
  · exact reaches_outcome_steps hst (reaches_outcome.of_outcome hout)

/-- `segExit_chain_trap` carrying `EncFsCtx` across the seam. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segExit_chainFs_trap {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {x : WithStoresEncGhost} {R : SepProp}
    {s0 s : State} {next : State → Prop}
    (hfs : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncFsCtx_trap kit ikit C abs s0 s)
    (h1 : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s next)
    (h2 : ∀ s', CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncFsCtx_trap kit ikit C abs s0 s' → next s' →
      reaches_outcome (trTrapProgAt img.base C abs)
        (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord) x R s0 s') :
    reaches_outcome (trTrapProgAt img.base C abs)
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord) x R s0 s := by
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact reaches_outcome_steps hst (h2 sf (hfs.of_steps hst) hnext)
  · exact reaches_outcome_steps hst (reaches_outcome.of_outcome hout)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segExit_chainFs {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {x : WithStoresEncGhost} {R : SepProp}
    {s0 s : State} {next : State → Prop}
    (hfs : EncFsCtx kit ikit C ctl abs s0 s)
    (h1 : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s next)
    (h2 : ∀ s', EncFsCtx kit ikit C ctl abs s0 s' → next s' →
      reaches_outcome (tripleRatchetProgAt img.base C ctl abs)
        (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord) x R s0 s') :
    reaches_outcome (tripleRatchetProgAt img.base C ctl abs)
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord) x R s0 s := by
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact reaches_outcome_steps hst (h2 sf (hfs.of_steps hst) hnext)
  · exact reaches_outcome_steps hst (reaches_outcome.of_outcome hout)

/-- `session_message_encrypt_with_stores` satisfies `withStoresEncSpecV` with both kits' `envOk`
on the entry files from `EncSegsV`, given `KitFsOk`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStores_ok_of_segsV_fs_trap {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} (hEnv : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (hSegs : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncSegsV_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (trTrapProgAt img.base C abs)) :
    subroutine_ok (trTrapProgAt img.base C abs) (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img)
      (withEnvPre (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) := by
  refine Arm64.subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre0 hal => ?_
  obtain ⟨h0, hpre⟩ := withEnvPre_pre_elim hpre0
  rw [reaches_outcome_withEnvPre]
  have ⟨haddr_ss, haddr_id⟩ := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV_pre_addrOk hpre
  have hfs0 : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncFsCtx_trap kit ikit C abs s0 s0 := FsCtx.of_entry hKitFs h0
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segExit_chainFs_trap hfs0 (hSegs.load hEnv x R s0 hfs0 hpc hrun hal hpre) ?_
  rintro s hfs ⟨r, g, sess, hCur⟩
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segExit_chainFs_trap hfs (hSegs.fromS hEnv x r g sess R s0 s hCur) ?_
  rintro s hfs ⟨otr, taken, pqCap, pqPtr, hOtr⟩
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segExit_chainFs_trap hfs (hSegs.identity hEnv x r sess otr taken pqCap pqPtr R s0 s hOtr) ?_
  rintro s hfs ⟨k, hKey⟩
  have hCm : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s
      (fun s' => ∃ m otr' pqCap' pqPtr',
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CmStateV kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord x r sess otr taken k m otr'
          pqCap' pqPtr' R s0 s') := by
    cases hp : sess.pendingPreKey with
    | none => exact hSegs.signal hEnv x r sess otr taken pqCap pqPtr k R s0 s hp hKey
    | some _ =>
      exact hSegs.preKey hEnv x r sess otr taken pqCap pqPtr k R s0 s (by simp [hp]) hKey
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segExit_chainFs_trap hfs hCm ?_
  rintro s hfs ⟨m, otr', pqCap', pqPtr', hCmS⟩
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segExit_chainFs_trap hfs
    (hSegs.trust hEnv x r sess otr taken k m otr' pqCap' pqPtr' R s0 s haddr_id hfs hCmS) ?_
  intro s hfs hSave
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segExit_chainFs_trap hfs
    (hSegs.save hEnv x r sess otr taken k m otr' pqCap' pqPtr' R s0 s haddr_id hfs hSave) ?_
  rintro s hfs ⟨c, hApply⟩
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segExit_chainFs_trap hfs
    (hSegs.applyStore hEnv x r sess otr taken k m otr' pqCap' pqPtr' c R s0 s haddr_ss hfs hApply) ?_
  intro s _ hStored
  exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segExit_chain_trap (hSegs.finish hEnv x r sess otr taken k m otr' c R s0 s hStored)
    (fun _ hF => False.elim hF)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStores_ok_of_segsV_fs {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} (hEnv : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (hSegs : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncSegsV kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAt img.base C ctl abs)) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img)
      (withEnvPre (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) := by
  refine Arm64.subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre0 hal => ?_
  obtain ⟨h0, hpre⟩ := withEnvPre_pre_elim hpre0
  rw [reaches_outcome_withEnvPre]
  have ⟨haddr_ss, haddr_id⟩ := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV_pre_addrOk hpre
  have hfs0 : EncFsCtx kit ikit C ctl abs s0 s0 := FsCtx.of_entry hKitFs h0
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segExit_chainFs hfs0 (hSegs.load hEnv x R s0 hfs0 hpc hrun hal hpre) ?_
  rintro s hfs ⟨r, g, sess, hCur⟩
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segExit_chainFs hfs (hSegs.fromS hEnv x r g sess R s0 s hCur) ?_
  rintro s hfs ⟨otr, taken, pqCap, pqPtr, hOtr⟩
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segExit_chainFs hfs (hSegs.identity hEnv x r sess otr taken pqCap pqPtr R s0 s hOtr) ?_
  rintro s hfs ⟨k, hKey⟩
  have hCm : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s
      (fun s' => ∃ m otr' pqCap' pqPtr',
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CmStateV kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord x r sess otr taken k m otr'
          pqCap' pqPtr' R s0 s') := by
    cases hp : sess.pendingPreKey with
    | none => exact hSegs.signal hEnv x r sess otr taken pqCap pqPtr k R s0 s hp hKey
    | some _ =>
      exact hSegs.preKey hEnv x r sess otr taken pqCap pqPtr k R s0 s (by simp [hp]) hKey
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segExit_chainFs hfs hCm ?_
  rintro s hfs ⟨m, otr', pqCap', pqPtr', hCmS⟩
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segExit_chainFs hfs
    (hSegs.trust hEnv x r sess otr taken k m otr' pqCap' pqPtr' R s0 s haddr_id hfs hCmS) ?_
  intro s hfs hSave
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segExit_chainFs hfs
    (hSegs.save hEnv x r sess otr taken k m otr' pqCap' pqPtr' R s0 s haddr_id hfs hSave) ?_
  rintro s hfs ⟨c, hApply⟩
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segExit_chainFs hfs
    (hSegs.applyStore hEnv x r sess otr taken k m otr' pqCap' pqPtr' c R s0 s haddr_ss hfs hApply) ?_
  intro s _ hStored
  exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segExit_chain (hSegs.finish hEnv x r sess otr taken k m otr' c R s0 s hStored)
    (fun _ hF => False.elim hF)

/-- `session_message_encrypt_with_stores` satisfies `withStoresEncSpecV` from `EncSegsV`
when both kits have trivial `envOk`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStores_ok_of_segsV_trap {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} (hEnv : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (hSegs : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncSegsV_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (trTrapProgAt img.base C abs) (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img)
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord) :=
  subroutine_ok_of_withEnvPre (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStores_ok_of_segsV_fs_trap hEnv hSegs (.inl htriv))
    fun s => htriv s.fs.files

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStores_ok_of_segsV {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} (hEnv : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (hSegs : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncSegsV kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img)
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord) :=
  subroutine_ok_of_withEnvPre (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStores_ok_of_segsV_fs hEnv hSegs (.inl htriv))
    fun s => htriv s.fs.files

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encSegsV_ok_trap {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncSegsV_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs :=
  ⟨CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segLoad_okV_trap, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segFrom_okV_trap, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segIdentity_okV_trap, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segSignal_okV_trap, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segPreKey_okV_trap,
   CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segTrust_okV_trap, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segSave_okV_trap, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segApplyStore_okV_trap, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segFinish_okV_trap⟩

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encSegsV_ok {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncSegsV kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs :=
  ⟨CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segLoad_okV, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segFrom_okV, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segIdentity_okV, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segSignal_okV, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segPreKey_okV,
   CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segTrust_okV, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segSave_okV, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segApplyStore_okV, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segFinish_okV⟩

/-- Top-level `session_message_encrypt_with_stores` contract for arbitrary session and identity
stores with trivial `envOk`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStores_okV_trap {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} (hEnv : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (trTrapProgAt img.base C abs) (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img)
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord) :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStores_ok_of_segsV_trap hEnv CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encSegsV_ok_trap htriv

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStores_okV {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} (hEnv : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img)
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord) :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStores_ok_of_segsV hEnv CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encSegsV_ok htriv

/-- Top-level `session_message_encrypt_with_stores` contract preserving both kits' `envOk`
on the entry files, given `KitFsOk`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStores_okV_fs_trap {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} (hEnv : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (trTrapProgAt img.base C abs)) :
    subroutine_ok (trTrapProgAt img.base C abs) (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img)
      (withEnvPre (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStores_ok_of_segsV_fs_trap hEnv CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encSegsV_ok_trap hKitFs

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStores_okV_fs {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} (hEnv : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (tripleRatchetProgAt img.base C ctl abs)) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img)
      (withEnvPre (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStores_ok_of_segsV_fs hEnv CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encSegsV_ok hKitFs

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.guard_withStores_okV_trap
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    (hEnv : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f) :
    subroutine_ok (trTrapProgAt img.base C abs) (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img)
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord) :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStores_okV_trap hEnv htriv

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.guard_withStores_okV
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    (hEnv : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img)
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord) :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStores_okV hEnv htriv

section CliCorollaries

open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Slots ProofLib.Variant

/-- Instantiate `withStores_okV_trap` on `tripleRatchetProgAtExt img.base (cliExterns W)`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStores_okV_cli_trap
    {img : Obj.Image} {W : CliHooks}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    (hEnv : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q
      W.C ctl uuidTryParse S encRecord (cliExterns W))
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr
        CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName)
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 W.C ctl uuidTryParse S encRecord) := by
  apply subroutine_ok_cli_of_trTrap
  rw [← entryOf_eq_tripleRatchetProgAt_trap (C := W.C) (abs := cliExterns W) hEnv.loads
    CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName]
  exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStores_okV_trap hEnv htriv

/-- Instantiate `withStores_okV_fs_trap` on `tripleRatchetProgAtExt img.base (cliExterns W)`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStores_okV_fs_cli_trap
    {img : Obj.Image} {W : CliHooks}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    (hEnv : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q
      W.C ctl uuidTryParse S encRecord (cliExterns W))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (trTrapProgAt img.base W.C (cliExterns W))) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      ((tripleRatchetProgAtExt img.base (cliExterns W)).fnAddr
        CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName)
      (withEnvPre (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 W.C ctl uuidTryParse S encRecord)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) := by
  apply subroutine_ok_cli_of_trTrap
  rw [← entryOf_eq_tripleRatchetProgAt_trap (C := W.C) (abs := cliExterns W) hEnv.loads
    CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName]
  exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStores_okV_fs_trap hEnv hKitFs

/-- Instantiate `withStores_okV_cli_trap` at `encEntry img`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStores_okV_encEntry_cli_trap
    {img : Obj.Image} {W : CliHooks}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    (hEnv : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q
      W.C ctl uuidTryParse S encRecord (cliExterns W))
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img)
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 W.C ctl uuidTryParse S encRecord) :=
  subroutine_ok.of_trapsOnly (trapsOnly_trTrap_cli img.base W)
    (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStores_okV_trap hEnv htriv)

/-- Instantiate `withStores_okV_fs_cli_trap` at `encEntry img`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStores_okV_fs_encEntry_cli_trap
    {img : Obj.Image} {W : CliHooks}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    (hEnv : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q
      W.C ctl uuidTryParse S encRecord (cliExterns W))
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
      (trTrapProgAt img.base W.C (cliExterns W))) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExterns W))
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img)
      (withEnvPre (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 W.C ctl uuidTryParse S encRecord)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) :=
  subroutine_ok.of_trapsOnly (trapsOnly_trTrap_cli img.base W)
    (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStores_okV_fs_trap hEnv hKitFs)

end CliCorollaries

end CryptoVerification.LibsignalPublicApi.MessageEncrypt

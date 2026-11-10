/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromHelpers
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget

/-!
# W1 `message_encrypt` Segment and `OutgoingTripleRatchet::encrypt` Bounds

Segment-level `PhaseCreditSpec` bounds for W1 `message_encrypt`, parametric in `(M : AllocCostModel)
[HasFineReallocCredit M]` under `ModelHyps M` in binary call order: atomic box/clone/Kyber envelopes,
boxed-future store steps, `OutgoingTripleRatchet::apply_to_session_state`,
`OutgoingTripleRatchet::encrypt`, and the `WithStoresEnc` segment chain.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.W1EncryptSegments

open CryptoGames.LibsignalSession (IdentityKey)
open CryptoGames.LibsignalSessionApi (Direction SessionRecord)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalSessionRepr (VecGhost)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalPublicApi.StoreKit (IdentityStoreSpec SessionStoreSpec)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (StringCloneEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
  (LoadStepEnv SessionStoreBudgetEnv StoreStepEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
  (IdentityStoreBudgetEnv SaveStepEnv TrustStepEnv)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (DeallocCreditSpec ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromHelpers
  (tryCloneLargeDelta tryCloneSmallDelta)

/-! ## 1. Atomic W1 Envelopes -/

/-- Allocation envelope for `Option<(KyberPreKeyId, &[u8])>::map(KyberPayload::new)`. -/
def KyberOptStepEnv (ct : Option (List (BitVec 8))) (evs : List AllocEvent) : Prop :=
  match ct with
  | none => evs = []
  | some bs =>
    (bs.length = 0 ∧ evs = []) ∨
    (0 < bs.length ∧ evs = rustAllocEvents bs.length 1)

theorem boxAlloc_creditSpec_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (boxSize : Nat) :
    PhaseCreditSpec M (BoxAllocEnv boxSize)
      (2 * boxSize + 9539) (boxSize + 8195) (boxSize + 8195) boxSize := by
  refine (PhaseCreditSpec.or_of_imp
    (E₁ := (· = [])) (E₂ := (· = rustAllocEvents boxSize 8))
    (fun _ h => h.elim (fun h0 => Or.inl h0.2) (fun h1 => Or.inr h1.2))
    (PhaseCreditSpec.nil M)
    (PhaseCreditSpec.rustAlloc_aff hM (req := boxSize) (al := 8) (by decide))).mono
    (by omega) (by omega) (by omega) (by omega)

theorem boxAlloc_creditSpec_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {boxSize : Nat}
    (hle : boxSize ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (BoxAllocEnv boxSize) (2 * boxSize + 9539) 0 0 boxSize := by
  have halloc : PhaseCreditSpec M (· = rustAllocEvents boxSize 8)
      (2 * boxSize + 9539) 0 0 boxSize :=
    (PhaseCreditSpec.rustAlloc_small_any hM (req := boxSize) (al := 8) (by decide) hle).mono
      (hM.smallAlloc_le hle) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl boxSize)
  refine (PhaseCreditSpec.or_of_imp
    (E₁ := (· = [])) (E₂ := (· = rustAllocEvents boxSize 8))
    (fun _ h => h.elim (fun h0 => Or.inl h0.2) (fun h1 => Or.inr h1.2))
    (PhaseCreditSpec.nil M) halloc).mono
    (by omega) (by omega) (by omega) (by omega)

theorem stringClone_creditSpec_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {g : VecGhost} {cap : Nat} (hcap : g.bytes.length ≤ cap) :
    PhaseCreditSpec M (StringCloneEnv g)
      (2 * cap + 9539) (cap + 8195) (cap + 8195) cap := by
  refine (PhaseCreditSpec.or_of_imp
    (E₁ := (· = [])) (E₂ := (· = rustAllocEvents g.bytes.length 1))
    (fun _ h => h.elim (fun h0 => Or.inl h0.2) (fun h1 => Or.inr h1.2))
    (PhaseCreditSpec.nil M)
    (PhaseCreditSpec.rustAlloc_aff hM (req := g.bytes.length) (al := 1) (by decide))).mono
    (by omega) (by omega) (by omega) (by omega)

theorem stringClone_creditSpec_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {g : VecGhost} {cap : Nat}
    (hcap : g.bytes.length ≤ cap) (hle : cap ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (StringCloneEnv g) (2 * cap + 9539) 0 0 cap := by
  have hg_le : g.bytes.length ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hcap hle
  have halloc : PhaseCreditSpec M (· = rustAllocEvents g.bytes.length 1)
      (2 * cap + 9539) 0 0 cap :=
    (PhaseCreditSpec.rustAlloc_small_any hM (req := g.bytes.length) (al := 1) (by decide) hg_le).mono
      (Nat.le_trans (hM.smallAlloc_le hg_le) (by omega))
      (Nat.le_refl 0) (Nat.le_refl 0) hcap
  refine (PhaseCreditSpec.or_of_imp
    (E₁ := (· = [])) (E₂ := (· = rustAllocEvents g.bytes.length 1))
    (fun _ h => h.elim (fun h0 => Or.inl h0.2) (fun h1 => Or.inr h1.2))
    (PhaseCreditSpec.nil M) halloc).mono
    (by omega) (by omega) (by omega) (by omega)

theorem stringCloneFree_creditSpec_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {g : VecGhost} {cap : Nat} (hcap : g.bytes.length ≤ cap) :
    PhaseCreditSpec M (SeqEnv (StringCloneEnv g) FreeOnlyEvs)
      (2 * cap + 9539) (cap + 8195) (cap + 8195) cap := by
  exact ((stringClone_creditSpec_aff hM hcap).seq (PhaseCreditSpec.freeOnly hM.freeNonInc)).mono
    (by omega) (by omega) (by omega) (by omega)

theorem stringCloneFree_creditSpec_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {g : VecGhost} {cap : Nat}
    (hcap : g.bytes.length ≤ cap) (hle : cap ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (SeqEnv (StringCloneEnv g) FreeOnlyEvs)
      (2 * cap + 9539) 0 0 cap := by
  exact ((stringClone_creditSpec_small hM hcap hle).seq (PhaseCreditSpec.freeOnly hM.freeNonInc)).mono
    (by omega) (by omega) (by omega) (by omega)

theorem kyberOpt_creditSpec_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {ct : Option (List (BitVec 8))} {ctCap : Nat}
    (hcap : ∀ bs, ct = some bs → bs.length ≤ ctCap) :
    PhaseCreditSpec M (KyberOptStepEnv ct)
      (2 * ctCap + 9539) (ctCap + 8195) (ctCap + 8195) ctCap := by
  cases ct with
  | none =>
    exact (PhaseCreditSpec.nil M).mono (by omega) (by omega) (by omega) (by omega)
  | some bs =>
    have hbs : bs.length ≤ ctCap := hcap bs rfl
    refine (PhaseCreditSpec.or_of_imp
      (E₁ := (· = [])) (E₂ := (· = rustAllocEvents bs.length 1))
      (fun _ h => h.elim (fun h0 => Or.inl h0.2) (fun h1 => Or.inr h1.2))
      (PhaseCreditSpec.nil M)
      (PhaseCreditSpec.rustAlloc_aff hM (req := bs.length) (al := 1) (by decide))).mono
      (by omega) (by omega) (by omega) (by omega)

theorem kyberOpt_creditSpec_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {ct : Option (List (BitVec 8))} {ctCap : Nat}
    (hcap : ∀ bs, ct = some bs → bs.length ≤ ctCap)
    (hle : ctCap ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (KyberOptStepEnv ct) (2 * ctCap + 9539) 0 0 ctCap := by
  cases ct with
  | none =>
    exact (PhaseCreditSpec.nil M).mono (by omega) (by omega) (by omega) (by omega)
  | some bs =>
    have hbs : bs.length ≤ ctCap := hcap bs rfl
    have hbs_sm : bs.length ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hbs hle
    have halloc : PhaseCreditSpec M (· = rustAllocEvents bs.length 1)
        (2 * ctCap + 9539) 0 0 ctCap :=
      (PhaseCreditSpec.rustAlloc_small_any hM (req := bs.length) (al := 1) (by decide) hbs_sm).mono
        (Nat.le_trans (hM.smallAlloc_le hbs_sm) (by omega))
        (Nat.le_refl 0) (Nat.le_refl 0) hbs
    refine (PhaseCreditSpec.or_of_imp
      (E₁ := (· = [])) (E₂ := (· = rustAllocEvents bs.length 1))
      (fun _ h => h.elim (fun h0 => Or.inl h0.2) (fun h1 => Or.inr h1.2))
      (PhaseCreditSpec.nil M) halloc).mono
      (by omega) (by omega) (by omega) (by omega)

/-! ## 2. Boxed-Future Store Step Envelopes -/

/-- Appends a trailing `FreeOnlyEvs`-implied phase via `SeqEnv` without requiring `Δlive ≤ Δpeak` on `hwork`.
-/
theorem seq_freeOnly {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {E_work E_free : List AllocEvent → Prop} {c l p r : Nat}
    (hwork : PhaseCreditSpec M E_work c l p r)
    (hfree : ∀ evs, E_free evs → FreeOnlyEvs evs) :
    PhaseCreditSpec M (SeqEnv E_work E_free) c l p r :=
  (PhaseCreditSpec.or hwork
    (hwork.concat_dealloc_cancel
      (DeallocCreditSpec.of_imp hfree (DeallocCreditSpec.freeOnly_of_hyps hM)))).mono
    (by omega) (by omega) (by omega) (by omega)

/-- Boxed-future `shim ++ poll ++ Box::drop` bound in binary call order. -/
theorem boxPollDrop_creditSpec_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {boxSize : Nat} {E_poll : List AllocEvent → Prop}
    {c_p l_p p_p r_p : Nat}
    (hpoll : PhaseCreditSpec M E_poll c_p l_p p_p r_p) :
    PhaseCreditSpec M
      (SeqEnv (BoxAllocEnv boxSize) (SeqEnv E_poll (· = rustDeallocEvents boxSize 8)))
      (2 * boxSize + 9539 + c_p)
      (boxSize + 8195 + l_p)
      (boxSize + 8195 + p_p)
      (max boxSize r_p) := by
  have h23 := seq_freeOnly (E_free := (· = rustDeallocEvents boxSize 8)) hM hpoll
    (fun _ h => by subst h; exact FreeOnlyEvs.singleton 8 boxSize)
  have h123 := (boxAlloc_creditSpec_aff hM boxSize).seq h23
  exact h123.mono (by omega) (by omega) (by omega) (by omega)

/-- Small-box (`boxSize ≤ smallMaxReq M`) boxed-future `shim ++ poll ++ Box::drop` bound (`0` box overhead on `Δlive` and `Δpeak`).
-/
theorem boxPollDrop_creditSpec_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {boxSize : Nat} {E_poll : List AllocEvent → Prop}
    {c_p l_p p_p r_p : Nat}
    (hbox : boxSize ≤ HasFineReallocCredit.smallMaxReq M)
    (hpoll : PhaseCreditSpec M E_poll c_p l_p p_p r_p) :
    PhaseCreditSpec M
      (SeqEnv (BoxAllocEnv boxSize) (SeqEnv E_poll (· = rustDeallocEvents boxSize 8)))
      (2 * boxSize + 9539 + c_p) l_p p_p (max boxSize r_p) := by
  have h23 := seq_freeOnly (E_free := (· = rustDeallocEvents boxSize 8)) hM hpoll
    (fun _ h => by subst h; exact FreeOnlyEvs.singleton 8 boxSize)
  have h123 := (boxAlloc_creditSpec_small hM hbox).seq h23
  exact h123.mono (by omega) (by omega) (by omega) (by omega)

theorem loadStep_creditSpec_aff {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustAlloc} {b : BitVec 64} (hM : ModelHyps M)
    (kit : SessionStoreSpec A b) (kitEnv : SessionStoreBudgetEnv kit)
    (st0 : kit.StoreState) (rem : AddrVal)
    {c_p l_p p_p r_p : Nat}
    (hpoll : PhaseCreditSpec M (kitEnv.loadPollEnv st0 rem) c_p l_p p_p r_p) :
    PhaseCreditSpec M (LoadStepEnv kit kitEnv st0 rem)
      (2 * kit.loadBoxSize + 9539 + c_p)
      (kit.loadBoxSize + 8195 + l_p)
      (kit.loadBoxSize + 8195 + p_p)
      (max kit.loadBoxSize r_p) :=
  boxPollDrop_creditSpec_aff hM hpoll

theorem storeStep_creditSpec_aff {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustAlloc} {b : BitVec 64} (hM : ModelHyps M)
    (kit : SessionStoreSpec A b) (kitEnv : SessionStoreBudgetEnv kit)
    (st0 : kit.StoreState) (rem : AddrVal) (rec : SessionRecord (List (BitVec 8)))
    {c_p l_p p_p r_p : Nat}
    (hpoll : PhaseCreditSpec M (kitEnv.storePollEnv st0 rem rec) c_p l_p p_p r_p) :
    PhaseCreditSpec M (StoreStepEnv kit kitEnv st0 rem rec)
      (2 * kit.storeBoxSize + 9539 + c_p)
      (kit.storeBoxSize + 8195 + l_p)
      (kit.storeBoxSize + 8195 + p_p)
      (max kit.storeBoxSize r_p) :=
  boxPollDrop_creditSpec_aff hM hpoll

theorem trustStep_creditSpec_aff {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustAlloc} {b : BitVec 64} (hM : ModelHyps M)
    (ikit : IdentityStoreSpec A b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (ist0 : ikit.IdState) (rem : AddrVal) (key : IdentityKey) (d : Direction)
    {c_p l_p p_p r_p : Nat}
    (hpoll : PhaseCreditSpec M (ikitEnv.trustPollEnv ist0 rem key d) c_p l_p p_p r_p) :
    PhaseCreditSpec M (TrustStepEnv ikit ikitEnv ist0 rem key d)
      (2 * ikit.trustBoxSize + 9539 + c_p)
      (ikit.trustBoxSize + 8195 + l_p)
      (ikit.trustBoxSize + 8195 + p_p)
      (max ikit.trustBoxSize r_p) :=
  boxPollDrop_creditSpec_aff hM hpoll

theorem saveStep_creditSpec_aff {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustAlloc} {b : BitVec 64} (hM : ModelHyps M)
    (ikit : IdentityStoreSpec A b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (ist0 : ikit.IdState) (rem : AddrVal) (key : IdentityKey)
    {c_p l_p p_p r_p : Nat}
    (hpoll : PhaseCreditSpec M (ikitEnv.savePollEnv ist0 rem key) c_p l_p p_p r_p) :
    PhaseCreditSpec M (SaveStepEnv ikit ikitEnv ist0 rem key)
      (2 * ikit.saveBoxSize + 9539 + c_p)
      (ikit.saveBoxSize + 8195 + l_p)
      (ikit.saveBoxSize + 8195 + p_p)
      (max ikit.saveBoxSize r_p) :=
  boxPollDrop_creditSpec_aff hM hpoll

/-! ## 3. `OutgoingTripleRatchet::apply_to_session_state` and `encrypt` Envelopes -/

/-- Allocation envelope of `OutgoingTripleRatchet::apply_to_session_state` (`32` B `ChainKey::to_pb` + chain drops).
-/
def OtrApplyEnvTight : List AllocEvent → Prop :=
  SeqEnv (· = rustAllocEvents 32 1) FreeOnlyEvs

theorem otrApply_creditSpec_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) :
    PhaseCreditSpec M OtrApplyEnvTight (2 * 32 + 9539) (32 + 8195) (32 + 8195) 32 := by
  exact ((PhaseCreditSpec.rustAlloc_aff hM (req := 32) (al := 1) (by decide)).seq
    (PhaseCreditSpec.freeOnly hM.freeNonInc)).mono
    (by omega) (by omega) (by omega) (by omega)

theorem otrApply_creditSpec_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hle32 : 32 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M OtrApplyEnvTight (2 * 32 + 9539) 0 0 32 := by
  have h32 : PhaseCreditSpec M (· = rustAllocEvents 32 1) (2 * 32 + 9539) 0 0 32 :=
    (PhaseCreditSpec.rustAlloc_small_any hM (req := 32) (al := 1) (by decide) hle32).mono
      (hM.smallAlloc_le hle32) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 32)
  exact (h32.seq (PhaseCreditSpec.freeOnly hM.freeNonInc)).mono
    (by omega) (by omega) (by omega) (by omega)

/-- Binary call-order allocation envelope of `OutgoingTripleRatchet::encrypt::<Coins>`:
`E_send` (`spqr::send`), followed on `Ok` by `OtrApplyEnvTight` (`32` B seed + drop),
AES-256-CBC PKCS#7 ciphertext `Vec<u8>`, `E_sigNew` (`SignalMessage::new`), and trailing drops. -/
def OtrEncryptStepEnv
    (E_send : List AllocEvent → Prop)
    (ptextLen : Nat)
    (E_sigNew : List AllocEvent → Prop) : List AllocEvent → Prop :=
  SeqEnv E_send
    (fun evs =>
      FreeOnlyEvs evs ∨
      SeqEnv OtrApplyEnvTight
        (SeqEnv (· = rustAllocEvents ((ptextLen / 16 + 1) * 16) 1)
          (SeqEnv E_sigNew FreeOnlyEvs)) evs)

theorem otrEncryptStep_creditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M)
    {E_send E_sigNew : List AllocEvent → Prop} {ptextLen : Nat}
    {c_s l_s p_s r_s c_n l_n p_n r_n : Nat}
    (hSend : PhaseCreditSpec M E_send c_s l_s p_s r_s)
    (hSigNew : PhaseCreditSpec M E_sigNew c_n l_n p_n r_n) :
    let ctLen := (ptextLen / 16 + 1) * 16
    PhaseCreditSpec M (OtrEncryptStepEnv E_send ptextLen E_sigNew)
      (c_s + (2 * 32 + 9539) + (2 * ctLen + 9539) + c_n)
      (l_s + (32 + 8195) + (ctLen + 8195) + l_n)
      (max p_s (l_s + (32 + 8195) + (ctLen + 8195) + p_n))
      (max r_s (max 32 (max ctLen r_n))) := by
  intro ctLen
  have hFree := PhaseCreditSpec.freeOnly hM.freeNonInc
  have hMkg := otrApply_creditSpec_aff hM
  have hCt := PhaseCreditSpec.rustAlloc_aff hM (req := ctLen) (al := 1) (by decide)
  have hTail1 := seq_freeOnly hM hSigNew (fun _ h => h)
  have hTail2 := hCt.seq hTail1
  have hOk := hMkg.seq hTail2
  have hBranch := PhaseCreditSpec.or hFree hOk
  have hAll := hSend.seq hBranch
  exact hAll.mono (by omega) (by omega) (by omega) (by omega)

/-! ## 4. Scoped Existential and `WithStoresEnc` Segment Composition -/

/-- Uniform `PhaseCreditSpec` across a guarded existential envelope `∃ w, P w ∧ E w evs`. -/
theorem phaseCreditSpec_exists {α : Type} {M : AllocCostModel} [HasFineReallocCredit M]
    {P : α → Prop} {E : α → List AllocEvent → Prop}
    {Δcum Δlive Δpeak maxReq : Nat}
    (h : ∀ w, P w → PhaseCreditSpec M (E w) Δcum Δlive Δpeak maxReq) :
    PhaseCreditSpec M (fun evs => ∃ w, P w ∧ E w evs) Δcum Δlive Δpeak maxReq where
  req_align := by
    rintro evs ⟨w, hw, hE⟩
    exact (h w hw).req_align evs hE
  credit_le := by
    rintro st0 _ ⟨w, hw, hE⟩
    exact (h w hw).credit_le st0 hE

/-- Parametric `FromApply` segment envelope (`OtrApplyEnvTight` + `store_session` step + exit drops).
-/
def FromApplySegEnv (boxStore : Nat) (E_storePoll : List AllocEvent → Prop) :
    List AllocEvent → Prop :=
  SeqEnv OtrApplyEnvTight
    (SeqEnv (BoxAllocEnv boxStore)
      (SeqEnv E_storePoll
        (SeqEnv (· = rustDeallocEvents boxStore 8) FreeOnlyEvs)))

theorem fromApplySeg_creditSpec_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {boxStore : Nat} {E_storePoll : List AllocEvent → Prop}
    {c_sp l_sp p_sp r_sp : Nat}
    (hStorePoll : PhaseCreditSpec M E_storePoll c_sp l_sp p_sp r_sp) :
    PhaseCreditSpec M (FromApplySegEnv boxStore E_storePoll)
      ((2 * 32 + 9539) + (2 * boxStore + 9539) + c_sp)
      ((32 + 8195) + (boxStore + 8195) + l_sp)
      ((32 + 8195) + (boxStore + 8195) + p_sp)
      (max 32 (max boxStore r_sp)) := by
  have hPollTail :=
    seq_freeOnly (E_free := SeqEnv (· = rustDeallocEvents boxStore 8) FreeOnlyEvs) hM hStorePoll
      fun evs h => by
        rcases h with rfl | ⟨_, _, rfl, rfl, hf⟩
        · exact FreeOnlyEvs.singleton 8 boxStore
        · exact fun e he => (List.mem_append.mp he).elim (FreeOnlyEvs.singleton 8 boxStore e) (hf e)
  have hStore := (boxAlloc_creditSpec_aff hM boxStore).seq hPollTail
  have hAll := (otrApply_creditSpec_aff hM).seq hStore
  exact hAll.mono (by omega) (by omega) (by omega) (by omega)

/-- Parametric `FromSave` segment envelope (`SaveStepEnv` + `(FreeOnlyEvs ∨ E_apply)`). -/
def FromSaveSegEnv (boxSave : Nat) (E_savePoll E_apply : List AllocEvent → Prop) :
    List AllocEvent → Prop :=
  SeqEnv (SeqEnv (BoxAllocEnv boxSave) (SeqEnv E_savePoll (· = rustDeallocEvents boxSave 8)))
    (fun evs => FreeOnlyEvs evs ∨ E_apply evs)

theorem fromSaveSeg_creditSpec_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {boxSave : Nat} {E_savePoll E_apply : List AllocEvent → Prop}
    {c_sv l_sv p_sv r_sv c_ap l_ap p_ap r_ap : Nat}
    (hSavePoll : PhaseCreditSpec M E_savePoll c_sv l_sv p_sv r_sv)
    (hApply : PhaseCreditSpec M E_apply c_ap l_ap p_ap r_ap) :
    PhaseCreditSpec M (FromSaveSegEnv boxSave E_savePoll E_apply)
      ((2 * boxSave + 9539 + c_sv) + c_ap)
      ((boxSave + 8195 + l_sv) + l_ap)
      (max (boxSave + 8195 + p_sv) ((boxSave + 8195 + l_sv) + p_ap))
      (max (max boxSave r_sv) r_ap) := by
  have hSave := boxPollDrop_creditSpec_aff hM (boxSize := boxSave) hSavePoll
  have hBranch := PhaseCreditSpec.or (PhaseCreditSpec.freeOnly hM.freeNonInc) hApply
  exact (hSave.seq hBranch).mono (by omega) (by omega) (by omega) (by omega)

/-- Parametric `FromCm` segment envelope (`TrustStepEnv` + `(FreeOnlyEvs ∨ StringClone ∨ E_save)`).
-/
def FromCmSegEnv (boxTrust : Nat) (E_trustPoll : List AllocEvent → Prop)
    (remName : VecGhost) (E_save : List AllocEvent → Prop) :
    List AllocEvent → Prop :=
  SeqEnv (SeqEnv (BoxAllocEnv boxTrust) (SeqEnv E_trustPoll (· = rustDeallocEvents boxTrust 8)))
    (fun evs =>
      FreeOnlyEvs evs ∨
      SeqEnv (StringCloneEnv remName) FreeOnlyEvs evs ∨
      E_save evs)

theorem fromCmSeg_creditSpec_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {boxTrust nameCap : Nat}
    {E_trustPoll E_save : List AllocEvent → Prop} {remName : VecGhost}
    {c_tr l_tr p_tr r_tr c_sv l_sv p_sv r_sv : Nat}
    (hName : remName.bytes.length ≤ nameCap)
    (hTrustPoll : PhaseCreditSpec M E_trustPoll c_tr l_tr p_tr r_tr)
    (hSave : PhaseCreditSpec M E_save c_sv l_sv p_sv r_sv) :
    PhaseCreditSpec M (FromCmSegEnv boxTrust E_trustPoll remName E_save)
      ((2 * boxTrust + 9539 + c_tr) + max (2 * nameCap + 9539) c_sv)
      ((boxTrust + 8195 + l_tr) + max (nameCap + 8195) l_sv)
      (max (boxTrust + 8195 + p_tr)
        ((boxTrust + 8195 + l_tr) + max (nameCap + 8195) p_sv))
      (max (max boxTrust r_tr) (max nameCap r_sv)) := by
  have hTrust := boxPollDrop_creditSpec_aff hM (boxSize := boxTrust) hTrustPoll
  have hClone := stringCloneFree_creditSpec_aff hM hName
  have hBr2 := PhaseCreditSpec.or hClone hSave
  have hBr1 := PhaseCreditSpec.or (PhaseCreditSpec.freeOnly hM.freeNonInc) hBr2
  exact (hTrust.seq hBr1).mono (by omega) (by omega) (by omega) (by omega)

/-- Parametric `FromKey` segment envelope covering both Signal (`none`) and PreKey (`some`) branches.
-/
def FromKeySegEnv {α : Type} (pendingPreKey : Option α)
    (remName : VecGhost) (kyberCt : Option (List (BitVec 8)))
    (E_otrNone E_cmNone E_otrSome E_pksmNew E_cmSome : List AllocEvent → Prop)
    (evs : List AllocEvent) : Prop :=
  (pendingPreKey = none ∧
    SeqEnv E_otrNone (fun evs' => FreeOnlyEvs evs' ∨ E_cmNone evs') evs) ∨
  (pendingPreKey.isSome ∧
    (SeqEnv (StringCloneEnv remName) FreeOnlyEvs evs ∨
      SeqEnv (KyberOptStepEnv kyberCt)
        (SeqEnv E_otrSome
          (fun evs' =>
            FreeOnlyEvs evs' ∨
            SeqEnv E_pksmNew (fun evs'' => FreeOnlyEvs evs'' ∨ E_cmSome evs'') evs')) evs))

theorem fromKeySeg_creditSpec_aff {α : Type} {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M)
    {pendingPreKey : Option α} {remName : VecGhost}
    {kyberCt : Option (List (BitVec 8))} {nameCap kyberCap : Nat}
    {E_otrNone E_cmNone E_otrSome E_pksmNew E_cmSome : List AllocEvent → Prop}
    {c_otr l_otr p_otr r_otr c_pk l_pk p_pk r_pk c_cm l_cm p_cm r_cm : Nat}
    (hName : remName.bytes.length ≤ nameCap)
    (hKyber : ∀ bs, kyberCt = some bs → bs.length ≤ kyberCap)
    (hOtrNone : PhaseCreditSpec M E_otrNone c_otr l_otr p_otr r_otr)
    (hOtrSome : PhaseCreditSpec M E_otrSome c_otr l_otr p_otr r_otr)
    (hPksmNew : PhaseCreditSpec M E_pksmNew c_pk l_pk p_pk r_pk)
    (hCmNone : PhaseCreditSpec M E_cmNone c_cm l_cm p_cm r_cm)
    (hCmSome : PhaseCreditSpec M E_cmSome c_cm l_cm p_cm r_cm) :
    PhaseCreditSpec M
      (FromKeySegEnv pendingPreKey remName kyberCt E_otrNone E_cmNone E_otrSome E_pksmNew E_cmSome)
      (max (2 * nameCap + 9539) ((2 * kyberCap + 9539) + c_otr + c_pk + c_cm))
      (max (nameCap + 8195) ((kyberCap + 8195) + l_otr + l_pk + l_cm))
      (max (nameCap + 8195)
        ((kyberCap + 8195) + max p_otr (l_otr + max p_pk (l_pk + p_cm))))
      (max nameCap (max kyberCap (max r_otr (max r_pk r_cm)))) := by
  have hFree := PhaseCreditSpec.freeOnly hM.freeNonInc
  -- Branch 1: `pendingPreKey = none` (`E_otrNone` ++ `(FreeOnlyEvs ∨ E_cmNone)`)
  have hNonePath := hOtrNone.seq (PhaseCreditSpec.or hFree hCmNone)
  -- Branch 2a: `pendingPreKey.isSome` early `StringClone` error
  have hClonePath := stringCloneFree_creditSpec_aff hM hName
  -- Branch 2b: `KyberOpt` ++ `E_otrSome` ++ `(FreeOnly ∨ (E_pksmNew ++ (FreeOnly ∨ E_cmSome)))`
  have hPkTail := hPksmNew.seq (PhaseCreditSpec.or hFree hCmSome)
  have hOtrTail := hOtrSome.seq (PhaseCreditSpec.or hFree hPkTail)
  have hSomeOk := (kyberOpt_creditSpec_aff hM hKyber).seq hOtrTail
  have hSomePath := PhaseCreditSpec.or hClonePath hSomeOk
  refine (PhaseCreditSpec.or_of_imp
    (himp := fun _ h => h.elim (fun h1 => Or.inl h1.2) (fun h2 => Or.inr h2.2))
    hNonePath hSomePath).mono (by omega) (by omega) (by omega) (by omega)

/-- Parametric top-level `WithStoresEnc` segment envelope. -/
def WithStoresEncSegEnv (boxLoad : Nat) (E_loadPoll : List AllocEvent → Prop)
    (remName : VecGhost) (E_fromOtr : List AllocEvent → Prop) :
    List AllocEvent → Prop :=
  SeqEnv (SeqEnv (BoxAllocEnv boxLoad) (SeqEnv E_loadPoll (· = rustDeallocEvents boxLoad 8)))
    (fun evs =>
      FreeOnlyEvs evs ∨
      SeqEnv (StringCloneEnv remName) FreeOnlyEvs evs ∨
      SeqEnv FreeOnlyEvs (fun evs' => FreeOnlyEvs evs' ∨ E_fromOtr evs') evs)

theorem withStoresEncSeg_creditSpec_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {boxLoad nameCap : Nat}
    {E_loadPoll E_fromOtr : List AllocEvent → Prop} {remName : VecGhost}
    {c_ld l_ld p_ld r_ld c_fo l_fo p_fo r_fo : Nat}
    (hName : remName.bytes.length ≤ nameCap)
    (hLoadPoll : PhaseCreditSpec M E_loadPoll c_ld l_ld p_ld r_ld)
    (hFromOtr : PhaseCreditSpec M E_fromOtr c_fo l_fo p_fo r_fo) :
    PhaseCreditSpec M (WithStoresEncSegEnv boxLoad E_loadPoll remName E_fromOtr)
      ((2 * boxLoad + 9539 + c_ld) + max (2 * nameCap + 9539) c_fo)
      ((boxLoad + 8195 + l_ld) + max (nameCap + 8195) l_fo)
      (max (boxLoad + 8195 + p_ld)
        ((boxLoad + 8195 + l_ld) + max (nameCap + 8195) p_fo))
      (max (max boxLoad r_ld) (max nameCap r_fo)) := by
  have hFree := PhaseCreditSpec.freeOnly hM.freeNonInc
  have hLoad := boxPollDrop_creditSpec_aff hM (boxSize := boxLoad) hLoadPoll
  have hClone := stringCloneFree_creditSpec_aff hM hName
  have hCur := hFree.seq (PhaseCreditSpec.or hFree hFromOtr)
  have hBr := PhaseCreditSpec.or hFree (PhaseCreditSpec.or hClone hCur)
  exact (hLoad.seq hBr).mono (by omega) (by omega) (by omega) (by omega)

/-! ## 5. Small-Box and Small-Name Specializations -/

theorem otrEncryptStep_creditSpec_small32 {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hle32 : 32 ≤ HasFineReallocCredit.smallMaxReq M)
    {E_send E_sigNew : List AllocEvent → Prop} {ptextLen : Nat}
    {c_s l_s p_s r_s c_n l_n p_n r_n : Nat}
    (hSend : PhaseCreditSpec M E_send c_s l_s p_s r_s)
    (hSigNew : PhaseCreditSpec M E_sigNew c_n l_n p_n r_n) :
    let ctLen := (ptextLen / 16 + 1) * 16
    PhaseCreditSpec M (OtrEncryptStepEnv E_send ptextLen E_sigNew)
      (c_s + (2 * 32 + 9539) + (2 * ctLen + 9539) + c_n)
      (l_s + (ctLen + 8195) + l_n)
      (max p_s (l_s + (ctLen + 8195) + p_n))
      (max r_s (max 32 (max ctLen r_n))) := by
  intro ctLen
  have hFree := PhaseCreditSpec.freeOnly hM.freeNonInc
  have hMkg := otrApply_creditSpec_small hM hle32
  have hCt := PhaseCreditSpec.rustAlloc_aff hM (req := ctLen) (al := 1) (by decide)
  have hOk := hMkg.seq (hCt.seq (seq_freeOnly hM hSigNew (fun _ h => h)))
  have hAll := hSend.seq (PhaseCreditSpec.or hFree hOk)
  exact hAll.mono (by omega) (by omega) (by omega) (by omega)

theorem fromApplySeg_creditSpec_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {boxStore : Nat} {E_storePoll : List AllocEvent → Prop}
    {c_sp l_sp p_sp r_sp : Nat}
    (hle32 : 32 ≤ HasFineReallocCredit.smallMaxReq M)
    (hbox : boxStore ≤ HasFineReallocCredit.smallMaxReq M)
    (hStorePoll : PhaseCreditSpec M E_storePoll c_sp l_sp p_sp r_sp) :
    PhaseCreditSpec M (FromApplySegEnv boxStore E_storePoll)
      ((2 * 32 + 9539) + (2 * boxStore + 9539) + c_sp)
      l_sp p_sp (max 32 (max boxStore r_sp)) := by
  have hPollTail :=
    seq_freeOnly (E_free := SeqEnv (· = rustDeallocEvents boxStore 8) FreeOnlyEvs) hM hStorePoll
      fun evs h => by
        rcases h with rfl | ⟨_, _, rfl, rfl, hf⟩
        · exact FreeOnlyEvs.singleton 8 boxStore
        · exact fun e he => (List.mem_append.mp he).elim (FreeOnlyEvs.singleton 8 boxStore e) (hf e)
  have hStore := (boxAlloc_creditSpec_small hM hbox).seq hPollTail
  exact ((otrApply_creditSpec_small hM hle32).seq hStore).mono
    (by omega) (by omega) (by omega) (by omega)

theorem fromSaveSeg_creditSpec_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {boxSave : Nat} {E_savePoll E_apply : List AllocEvent → Prop}
    {c_sv l_sv p_sv r_sv c_ap l_ap p_ap r_ap : Nat}
    (hbox : boxSave ≤ HasFineReallocCredit.smallMaxReq M)
    (hSavePoll : PhaseCreditSpec M E_savePoll c_sv l_sv p_sv r_sv)
    (hApply : PhaseCreditSpec M E_apply c_ap l_ap p_ap r_ap) :
    PhaseCreditSpec M (FromSaveSegEnv boxSave E_savePoll E_apply)
      ((2 * boxSave + 9539 + c_sv) + c_ap)
      (l_sv + l_ap)
      (max p_sv (l_sv + p_ap))
      (max (max boxSave r_sv) r_ap) := by
  have hSave := boxPollDrop_creditSpec_small hM hbox hSavePoll
  have hBranch := PhaseCreditSpec.or (PhaseCreditSpec.freeOnly hM.freeNonInc) hApply
  exact (hSave.seq hBranch).mono (by omega) (by omega) (by omega) (by omega)

theorem fromCmSeg_creditSpec_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {boxTrust nameCap : Nat}
    {E_trustPoll E_save : List AllocEvent → Prop} {remName : VecGhost}
    {c_tr l_tr p_tr r_tr c_sv l_sv p_sv r_sv : Nat}
    (hbox : boxTrust ≤ HasFineReallocCredit.smallMaxReq M)
    (hName : remName.bytes.length ≤ nameCap)
    (hNameSmall : nameCap ≤ HasFineReallocCredit.smallMaxReq M)
    (hTrustPoll : PhaseCreditSpec M E_trustPoll c_tr l_tr p_tr r_tr)
    (hSave : PhaseCreditSpec M E_save c_sv l_sv p_sv r_sv) :
    PhaseCreditSpec M (FromCmSegEnv boxTrust E_trustPoll remName E_save)
      ((2 * boxTrust + 9539 + c_tr) + max (2 * nameCap + 9539) c_sv)
      (l_tr + l_sv)
      (max p_tr (l_tr + p_sv))
      (max (max boxTrust r_tr) (max nameCap r_sv)) := by
  have hTrust := boxPollDrop_creditSpec_small hM hbox hTrustPoll
  have hClone := stringCloneFree_creditSpec_small hM hName hNameSmall
  have hBr := PhaseCreditSpec.or (PhaseCreditSpec.freeOnly hM.freeNonInc)
    (PhaseCreditSpec.or hClone hSave)
  exact (hTrust.seq hBr).mono (by omega) (by omega) (by omega) (by omega)

theorem withStoresEncSeg_creditSpec_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {boxLoad nameCap : Nat}
    {E_loadPoll E_fromOtr : List AllocEvent → Prop} {remName : VecGhost}
    {c_ld l_ld p_ld r_ld c_fo l_fo p_fo r_fo : Nat}
    (hbox : boxLoad ≤ HasFineReallocCredit.smallMaxReq M)
    (hName : remName.bytes.length ≤ nameCap)
    (hNameSmall : nameCap ≤ HasFineReallocCredit.smallMaxReq M)
    (hLoadPoll : PhaseCreditSpec M E_loadPoll c_ld l_ld p_ld r_ld)
    (hFromOtr : PhaseCreditSpec M E_fromOtr c_fo l_fo p_fo r_fo) :
    PhaseCreditSpec M (WithStoresEncSegEnv boxLoad E_loadPoll remName E_fromOtr)
      ((2 * boxLoad + 9539 + c_ld) + max (2 * nameCap + 9539) c_fo)
      (l_ld + l_fo)
      (max p_ld (l_ld + p_fo))
      (max (max boxLoad r_ld) (max nameCap r_fo)) := by
  have hFree := PhaseCreditSpec.freeOnly hM.freeNonInc
  have hLoad := boxPollDrop_creditSpec_small hM hbox hLoadPoll
  have hClone := stringCloneFree_creditSpec_small hM hName hNameSmall
  have hCur := hFree.seq (PhaseCreditSpec.or hFree hFromOtr)
  have hBr := PhaseCreditSpec.or hFree (PhaseCreditSpec.or hClone hCur)
  exact (hLoad.seq hBr).mono (by omega) (by omega) (by omega) (by omega)

/-! ## 6. Tight `smallAllocCost` and `tryCloneSmallDelta` Bounds -/

/-- Regime-split `PhaseCreditSpec` for `rustAllocEvents req al` (`al ≤ 16`, `0 < req`). -/
theorem rustAlloc_pos_creditSpec_tight (M : AllocCostModel) [HasFineReallocCredit M]
    {req al : Nat} (hal : al ≤ 16) (hpos : 0 < req) :
    PhaseCreditSpec M (· = rustAllocEvents req al)
      (tryCloneSmallDelta M req) (tryCloneLargeDelta M req) (tryCloneLargeDelta M req) req := by
  have hne : req ≠ 0 := by omega
  unfold tryCloneSmallDelta tryCloneLargeDelta
  simp only [hne, ↓reduceIte]
  by_cases hle : req ≤ HasFineReallocCredit.smallMaxReq M
  · simp only [hle, ↓reduceIte]
    exact PhaseCreditSpec.rustAlloc_small M hal hpos hle
  · simp only [hle, ↓reduceIte]
    exact PhaseCreditSpec.rustAlloc_large M hal (by omega)

theorem boxAlloc_creditSpec_tight (M : AllocCostModel) [HasFineReallocCredit M]
    {boxSize : Nat} (hle : boxSize ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (BoxAllocEnv boxSize)
      (HasFineReallocCredit.smallAllocCost M boxSize) 0 0 boxSize := by
  by_cases hpos : 0 < boxSize
  · have halloc :=
      PhaseCreditSpec.rustAlloc_small M (req := boxSize) (al := 8) (by decide) hpos hle
    exact (PhaseCreditSpec.or_of_imp
      (fun _ h => h.elim (fun h0 => Or.inl h0.2) (fun h1 => Or.inr h1.2))
      (PhaseCreditSpec.nil M) halloc).mono (by omega) (by omega) (by omega) (by omega)
  · refine (PhaseCreditSpec.of_eq_nil ?_).mono (by omega) (by omega) (by omega) (by omega)
    intro evs h
    rcases h with ⟨_, rfl⟩ | ⟨hp, _⟩
    · rfl
    · omega

/-- Small-regime `PhaseCreditSpec` for `StringCloneEnv g` under bucket upper bound `nameCum`. -/
theorem stringClone_creditSpec_tight (M : AllocCostModel) [HasFineReallocCredit M]
    {g : VecGhost} {cap nameCum : Nat}
    (hcap : g.bytes.length ≤ cap)
    (hle : cap ≤ HasFineReallocCredit.smallMaxReq M)
    (hcum : ∀ n, 0 < n → n ≤ cap → HasFineReallocCredit.smallAllocCost M n ≤ nameCum) :
    PhaseCreditSpec M (StringCloneEnv g) nameCum 0 0 cap := by
  by_cases hpos : 0 < g.bytes.length
  · have hg_sm : g.bytes.length ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hcap hle
    have halloc : PhaseCreditSpec M (· = rustAllocEvents g.bytes.length 1) nameCum 0 0 cap :=
      (PhaseCreditSpec.rustAlloc_small M (req := g.bytes.length) (al := 1)
        (by decide) hpos hg_sm).mono
        (hcum g.bytes.length hpos hcap) (Nat.le_refl 0) (Nat.le_refl 0) hcap
    exact (PhaseCreditSpec.or_of_imp
      (fun _ h => h.elim (fun h0 => Or.inl h0.2) (fun h1 => Or.inr h1.2))
      (PhaseCreditSpec.nil M) halloc).mono (by omega) (by omega) (by omega) (by omega)
  · refine (PhaseCreditSpec.of_eq_nil ?_).mono (by omega) (by omega) (by omega) (by omega)
    intro evs h
    rcases h with ⟨_, rfl⟩ | ⟨hp, _⟩
    · rfl
    · omega

theorem stringCloneFree_creditSpec_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {g : VecGhost} {cap nameCum : Nat}
    (hcap : g.bytes.length ≤ cap)
    (hle : cap ≤ HasFineReallocCredit.smallMaxReq M)
    (hcum : ∀ n, 0 < n → n ≤ cap → HasFineReallocCredit.smallAllocCost M n ≤ nameCum) :
    PhaseCreditSpec M (SeqEnv (StringCloneEnv g) FreeOnlyEvs) nameCum 0 0 cap := by
  exact ((stringClone_creditSpec_tight M hcap hle hcum).seq
    (PhaseCreditSpec.freeOnly hM.freeNonInc)).mono (by omega) (by omega) (by omega) (by omega)

/-- Exact-size small-regime (`ctLen ≤ smallMaxReq M`) `PhaseCreditSpec` for `KyberOptStepEnv ct`. -/
theorem kyberOpt_creditSpec_eq_tight (M : AllocCostModel) [HasFineReallocCredit M]
    {ct : Option (List (BitVec 8))} {ctLen : Nat}
    (heq : ∀ bs, ct = some bs → bs.length = ctLen)
    (hle : ctLen ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (KyberOptStepEnv ct)
      (HasFineReallocCredit.smallAllocCost M ctLen) 0 0 ctLen := by
  cases ct with
  | none =>
    exact (PhaseCreditSpec.nil M).mono (by omega) (by omega) (by omega) (by omega)
  | some bs =>
    have hbs : bs.length = ctLen := heq bs rfl
    by_cases hpos : 0 < ctLen
    · have halloc : PhaseCreditSpec M (· = rustAllocEvents bs.length 1)
          (HasFineReallocCredit.smallAllocCost M ctLen) 0 0 ctLen := by
        rw [hbs]
        exact PhaseCreditSpec.rustAlloc_small M (req := ctLen) (al := 1) (by decide) hpos hle
      exact (PhaseCreditSpec.or_of_imp
        (fun _ h => h.elim (fun h0 => Or.inl h0.2) (fun h1 => Or.inr h1.2))
        (PhaseCreditSpec.nil M) halloc).mono (by omega) (by omega) (by omega) (by omega)
    · refine (PhaseCreditSpec.of_eq_nil ?_).mono (by omega) (by omega) (by omega) (by omega)
      intro evs h
      rcases h with ⟨_, rfl⟩ | ⟨hp, _⟩
      · rfl
      · omega

theorem boxPollDrop_creditSpec_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {boxSize : Nat} {E_poll : List AllocEvent → Prop}
    {c_p l_p p_p r_p : Nat}
    (hbox : boxSize ≤ HasFineReallocCredit.smallMaxReq M)
    (hpoll : PhaseCreditSpec M E_poll c_p l_p p_p r_p) :
    PhaseCreditSpec M
      (SeqEnv (BoxAllocEnv boxSize) (SeqEnv E_poll (· = rustDeallocEvents boxSize 8)))
      (HasFineReallocCredit.smallAllocCost M boxSize + c_p) l_p p_p (max boxSize r_p) := by
  have h23 := seq_freeOnly (E_free := (· = rustDeallocEvents boxSize 8)) hM hpoll
    (fun _ h => by subst h; exact FreeOnlyEvs.singleton 8 boxSize)
  have h123 := (boxAlloc_creditSpec_tight M hbox).seq h23
  exact h123.mono (by omega) (by omega) (by omega) (by omega)

theorem otrApply_creditSpec_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hle32 : 32 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M OtrApplyEnvTight
      (HasFineReallocCredit.smallAllocCost M 32) 0 0 32 := by
  have h32 := PhaseCreditSpec.rustAlloc_small M (req := 32) (al := 1) (by decide) (by decide) hle32
  exact (h32.seq (PhaseCreditSpec.freeOnly hM.freeNonInc)).mono
    (by omega) (by omega) (by omega) (by omega)

/-- Tight `PhaseCreditSpec` for `OtrEncryptStepEnv` using `smallAllocCost M 32` and `tryCloneSmallDelta` / `tryCloneLargeDelta`.
-/
theorem otrEncryptStep_creditSpec_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hle32 : 32 ≤ HasFineReallocCredit.smallMaxReq M)
    {E_send E_sigNew : List AllocEvent → Prop} {ptextLen : Nat}
    {c_s l_s p_s r_s c_n l_n p_n r_n : Nat}
    (hSend : PhaseCreditSpec M E_send c_s l_s p_s r_s)
    (hSigNew : PhaseCreditSpec M E_sigNew c_n l_n p_n r_n) :
    let ctLen := (ptextLen / 16 + 1) * 16
    PhaseCreditSpec M (OtrEncryptStepEnv E_send ptextLen E_sigNew)
      (c_s + HasFineReallocCredit.smallAllocCost M 32 + tryCloneSmallDelta M ctLen + c_n)
      (l_s + tryCloneLargeDelta M ctLen + l_n)
      (max p_s (l_s + tryCloneLargeDelta M ctLen + p_n))
      (max r_s (max 32 (max ctLen r_n))) := by
  intro ctLen
  have hct_pos : 0 < ctLen := by dsimp only [ctLen]; omega
  have hFree := PhaseCreditSpec.freeOnly hM.freeNonInc
  have hMkg := otrApply_creditSpec_tight hM hle32
  have hCt := rustAlloc_pos_creditSpec_tight M (req := ctLen) (al := 1) (by decide) hct_pos
  have hOk := hMkg.seq (hCt.seq (seq_freeOnly hM hSigNew (fun _ h => h)))
  have hAll := hSend.seq (PhaseCreditSpec.or hFree hOk)
  exact hAll.mono (by omega) (by omega) (by omega) (by omega)

theorem fromApplySeg_creditSpec_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {boxStore : Nat} {E_storePoll : List AllocEvent → Prop}
    {c_sp l_sp p_sp r_sp : Nat}
    (hle32 : 32 ≤ HasFineReallocCredit.smallMaxReq M)
    (hbox : boxStore ≤ HasFineReallocCredit.smallMaxReq M)
    (hStorePoll : PhaseCreditSpec M E_storePoll c_sp l_sp p_sp r_sp) :
    PhaseCreditSpec M (FromApplySegEnv boxStore E_storePoll)
      (HasFineReallocCredit.smallAllocCost M 32 +
        HasFineReallocCredit.smallAllocCost M boxStore + c_sp)
      l_sp p_sp (max 32 (max boxStore r_sp)) := by
  have hPollTail :=
    seq_freeOnly (E_free := SeqEnv (· = rustDeallocEvents boxStore 8) FreeOnlyEvs) hM hStorePoll
      fun evs h => by
        rcases h with rfl | ⟨_, _, rfl, rfl, hf⟩
        · exact FreeOnlyEvs.singleton 8 boxStore
        · exact fun e he => (List.mem_append.mp he).elim (FreeOnlyEvs.singleton 8 boxStore e) (hf e)
  have hStore := (boxAlloc_creditSpec_tight M hbox).seq hPollTail
  exact ((otrApply_creditSpec_tight hM hle32).seq hStore).mono
    (by omega) (by omega) (by omega) (by omega)

theorem fromSaveSeg_creditSpec_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {boxSave : Nat} {E_savePoll E_apply : List AllocEvent → Prop}
    {c_sv l_sv p_sv r_sv c_ap l_ap p_ap r_ap : Nat}
    (hbox : boxSave ≤ HasFineReallocCredit.smallMaxReq M)
    (hSavePoll : PhaseCreditSpec M E_savePoll c_sv l_sv p_sv r_sv)
    (hApply : PhaseCreditSpec M E_apply c_ap l_ap p_ap r_ap) :
    PhaseCreditSpec M (FromSaveSegEnv boxSave E_savePoll E_apply)
      ((HasFineReallocCredit.smallAllocCost M boxSave + c_sv) + c_ap)
      (l_sv + l_ap)
      (max p_sv (l_sv + p_ap))
      (max (max boxSave r_sv) r_ap) := by
  have hSave := boxPollDrop_creditSpec_tight hM hbox hSavePoll
  have hBranch := PhaseCreditSpec.or (PhaseCreditSpec.freeOnly hM.freeNonInc) hApply
  exact (hSave.seq hBranch).mono (by omega) (by omega) (by omega) (by omega)

theorem fromCmSeg_creditSpec_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {boxTrust nameCap nameCum : Nat}
    {E_trustPoll E_save : List AllocEvent → Prop} {remName : VecGhost}
    {c_tr l_tr p_tr r_tr c_sv l_sv p_sv r_sv : Nat}
    (hbox : boxTrust ≤ HasFineReallocCredit.smallMaxReq M)
    (hName : remName.bytes.length ≤ nameCap)
    (hNameSmall : nameCap ≤ HasFineReallocCredit.smallMaxReq M)
    (hNameCum : ∀ n, 0 < n → n ≤ nameCap → HasFineReallocCredit.smallAllocCost M n ≤ nameCum)
    (hTrustPoll : PhaseCreditSpec M E_trustPoll c_tr l_tr p_tr r_tr)
    (hSave : PhaseCreditSpec M E_save c_sv l_sv p_sv r_sv) :
    PhaseCreditSpec M (FromCmSegEnv boxTrust E_trustPoll remName E_save)
      ((HasFineReallocCredit.smallAllocCost M boxTrust + c_tr) + max nameCum c_sv)
      (l_tr + l_sv)
      (max p_tr (l_tr + p_sv))
      (max (max boxTrust r_tr) (max nameCap r_sv)) := by
  have hTrust := boxPollDrop_creditSpec_tight hM hbox hTrustPoll
  have hClone := stringCloneFree_creditSpec_tight hM hName hNameSmall hNameCum
  have hBr := PhaseCreditSpec.or (PhaseCreditSpec.freeOnly hM.freeNonInc)
    (PhaseCreditSpec.or hClone hSave)
  exact (hTrust.seq hBr).mono (by omega) (by omega) (by omega) (by omega)

/-- Tight `FromKeySegEnv` bound when `kyberCt` has exact byte length `kyberLen ≤ smallMaxReq M`. -/
theorem fromKeySeg_creditSpec_tight {α : Type} {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M)
    {pendingPreKey : Option α} {remName : VecGhost}
    {kyberCt : Option (List (BitVec 8))} {nameCap nameCum kyberLen : Nat}
    {E_otrNone E_cmNone E_otrSome E_pksmNew E_cmSome : List AllocEvent → Prop}
    {c_otr l_otr p_otr r_otr c_pk l_pk p_pk r_pk c_cm l_cm p_cm r_cm : Nat}
    (hName : remName.bytes.length ≤ nameCap)
    (hNameSmall : nameCap ≤ HasFineReallocCredit.smallMaxReq M)
    (hNameCum : ∀ n, 0 < n → n ≤ nameCap → HasFineReallocCredit.smallAllocCost M n ≤ nameCum)
    (hKyberEq : ∀ bs, kyberCt = some bs → bs.length = kyberLen)
    (hKyberSmall : kyberLen ≤ HasFineReallocCredit.smallMaxReq M)
    (hOtrNone : PhaseCreditSpec M E_otrNone c_otr l_otr p_otr r_otr)
    (hOtrSome : PhaseCreditSpec M E_otrSome c_otr l_otr p_otr r_otr)
    (hPksmNew : PhaseCreditSpec M E_pksmNew c_pk l_pk p_pk r_pk)
    (hCmNone : PhaseCreditSpec M E_cmNone c_cm l_cm p_cm r_cm)
    (hCmSome : PhaseCreditSpec M E_cmSome c_cm l_cm p_cm r_cm) :
    PhaseCreditSpec M
      (FromKeySegEnv pendingPreKey remName kyberCt E_otrNone E_cmNone E_otrSome E_pksmNew E_cmSome)
      (max nameCum (HasFineReallocCredit.smallAllocCost M kyberLen + c_otr + c_pk + c_cm))
      (l_otr + l_pk + l_cm)
      (max p_otr (l_otr + max p_pk (l_pk + p_cm)))
      (max nameCap (max kyberLen (max r_otr (max r_pk r_cm)))) := by
  have hFree := PhaseCreditSpec.freeOnly hM.freeNonInc
  have hNonePath := hOtrNone.seq (PhaseCreditSpec.or hFree hCmNone)
  have hClonePath := stringCloneFree_creditSpec_tight hM hName hNameSmall hNameCum
  have hPkTail := hPksmNew.seq (PhaseCreditSpec.or hFree hCmSome)
  have hOtrTail := hOtrSome.seq (PhaseCreditSpec.or hFree hPkTail)
  have hSomeOk := (kyberOpt_creditSpec_eq_tight M hKyberEq hKyberSmall).seq hOtrTail
  have hSomePath := PhaseCreditSpec.or hClonePath hSomeOk
  refine (PhaseCreditSpec.or_of_imp
    (himp := fun _ h => h.elim (fun h1 => Or.inl h1.2) (fun h2 => Or.inr h2.2))
    hNonePath hSomePath).mono (by omega) (by omega) (by omega) (by omega)

theorem withStoresEncSeg_creditSpec_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {boxLoad nameCap nameCum : Nat}
    {E_loadPoll E_fromOtr : List AllocEvent → Prop} {remName : VecGhost}
    {c_ld l_ld p_ld r_ld c_fo l_fo p_fo r_fo : Nat}
    (hbox : boxLoad ≤ HasFineReallocCredit.smallMaxReq M)
    (hName : remName.bytes.length ≤ nameCap)
    (hNameSmall : nameCap ≤ HasFineReallocCredit.smallMaxReq M)
    (hNameCum : ∀ n, 0 < n → n ≤ nameCap → HasFineReallocCredit.smallAllocCost M n ≤ nameCum)
    (hLoadPoll : PhaseCreditSpec M E_loadPoll c_ld l_ld p_ld r_ld)
    (hFromOtr : PhaseCreditSpec M E_fromOtr c_fo l_fo p_fo r_fo) :
    PhaseCreditSpec M (WithStoresEncSegEnv boxLoad E_loadPoll remName E_fromOtr)
      ((HasFineReallocCredit.smallAllocCost M boxLoad + c_ld) + max nameCum c_fo)
      (l_ld + l_fo)
      (max p_ld (l_ld + p_fo))
      (max (max boxLoad r_ld) (max nameCap r_fo)) := by
  have hFree := PhaseCreditSpec.freeOnly hM.freeNonInc
  have hLoad := boxPollDrop_creditSpec_tight hM hbox hLoadPoll
  have hClone := stringCloneFree_creditSpec_tight hM hName hNameSmall hNameCum
  have hCur := hFree.seq (PhaseCreditSpec.or hFree hFromOtr)
  have hBr := PhaseCreditSpec.or hFree (PhaseCreditSpec.or hClone hCur)
  exact (hLoad.seq hBr).mono (by omega) (by omega) (by omega) (by omega)

end LibsignalBinary.Proofs.PeakBudget.W1EncryptSegments

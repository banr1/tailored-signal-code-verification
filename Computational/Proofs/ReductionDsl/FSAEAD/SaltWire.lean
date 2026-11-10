/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.FSAEAD.SaltWireCosted
public import Computational.Proofs.ReductionDsl.Soundness
import Computational.Proofs.ReductionDsl.SimRel
import Computational.Proofs.ReductionDsl.Size
import Computational.Proofs.ReductionDsl.Tables
import Computational.Proofs.GameHop.StateSim

/-!
# Soundness and bounds for the costed Libsignal salt and wire reductions

Soundness (`eval`), query bounds, and size-honesty certificates for `lSaltRedProg`, `lWireRedProg`,
`slotSaltRedProg`, and `slotWireRedProg`.
-/

@[expose] public section

namespace CryptoGames.Ratchet.LibsignalInst.Costed

open ReductionDsl OracleComp OracleSpec CryptoGames CryptoGames.AEAD.Costed CryptoGames.OTCCA.Costed
  CryptoGames.PRF.Costed CryptoGames.Ratchet CryptoGames.Ratchet.LibsignalInst
  CryptoGames.LibsignalAead CryptoGames.LibsignalSession CryptoGames.SM.Construction
  CryptoGames.MACScheme CryptoGames.HKDF CBC

variable {Pt : Type} [DecidableEq Pt]
  (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
  (idOf : Party → IdentityKey) (kAEAD kIdeal : ℕ)

local notation "SWSig" => saltWireSig Pt ℓ
local notation "SWT" => Ty SWSig
local notation "SWOps" => saltWireOps C codec ℓ encT idOf kAEAD
local notation "SaltIface" => saltRedIface C codec ℓ encT kIdeal
local notation "WireIface" => wireRedIface Pt ℓ
local notation "SlotIface" => slotOtccaIface C codec ℓ encT kIdeal
local notation "SlotCodec" => slotOtccaCodec Pt ℓ

/-! ## Size-honesty certificates -/

omit [DecidableEq Pt] in
theorem lctTy_fits (k : ℕ) (hk : 1 ≤ k) (c : LibsignalCiphertextWithSalt32) :
    (lctTy Pt ℓ).Fits k c :=
  ⟨⟨hk, hk⟩, hk⟩

omit [DecidableEq Pt] in
theorem wireOps_sizeHonest : OpsSizeHonest (wireOps (Pt := Pt) ℓ encT idOf)
  | .idsOf, _, B, _ | .hdrOf, _, B, _ | .fitPlainOp, _, B, _ => by
    simp only [Ty.Fits]; omega
  | .eqHdr, _, _, _ => trivial

theorem saltWireOps_sizeHonest (hAEAD : 1 ≤ kAEAD) :
    OpsSizeHonest SWOps :=
  OpsSizeHonest.sum
    (CryptoGames.otccaOps_sizeHonest (S := SWSig) (.base .msgKey) (slotAdTy Pt ℓ) (slotAdTy Pt ℓ)
      (.base .plain) (lctTy Pt ℓ) (libsignalAeadKeyIndexedAd C codec ℓ encT idOf) kAEAD
      (.base .salt) (fun a => a.2.2.salt)
      (lctTy_fits ℓ kAEAD hAEAD) (fun _ => hAEAD) (fun _ => hAEAD))
    (OpsSizeHonest.sum
      (CryptoGames.otccaOps_sizeHonest (S := SWSig) (.base .seed) (slotAdTy Pt ℓ) (slotAdTy Pt ℓ)
        (.base .plain) (lctTy Pt ℓ) (lAeadR C codec ℓ encT idOf) kAEAD
        (.base .salt) (fun a => a.2.2.salt)
        (lctTy_fits ℓ kAEAD hAEAD) (fun _ => hAEAD) (fun _ => hAEAD))
      (wireOps_sizeHonest ℓ encT idOf))

omit [DecidableEq Pt] in
theorem saltRedIface_sampSizeHonest (hIdeal : 1 ≤ kIdeal) :
    SampSizeHonest (SaltIface).smp :=
  SampSizeHonest.sum
    (SampSizeHonest.sum SampSizeHonest.empty
      (CryptoGames.idealSamplers_sizeHonest (S := SWSig) (slotAdTy Pt ℓ) (lctTy Pt ℓ)
        (lIdeal C codec ℓ encT) kIdeal (fun _ c _ => lctTy_fits ℓ kIdeal hIdeal c)))
    (SampSizeHonest.unifSamplers0 SWSig)

omit [DecidableEq Pt] in
theorem wireRedIface_sampSizeHonest :
    SampSizeHonest (WireIface).smp :=
  SampSizeHonest.sum SampSizeHonest.empty (SampSizeHonest.unifSamplers0 SWSig)

omit [DecidableEq Pt] in
theorem slotOtccaIface_sampSizeHonest (hIdeal : 1 ≤ kIdeal) :
    SampSizeHonest (SlotIface).smp :=
  SampSizeHonest.sum
    (CryptoGames.idealSamplers_sizeHonest (S := SWSig) (slotAdTy Pt ℓ) (lctTy Pt ℓ)
      (lIdeal C codec ℓ encT) kIdeal (fun _ c _ => lctTy_fits ℓ kIdeal hIdeal c))
    (SampSizeHonest.unifSamplers (S := SWSig) slotKeySort (fun _ => 1))

/-! ## Interface, codec, and helper evaluation -/

omit [DecidableEq Pt] in
theorem prfIface_liftP {S : Sig} (inpT tagT : Ty S) {α : Type} (p : ProbComp α) :
    (prfIface inpT tagT).liftP p =
      (liftM p : OracleComp (unifSpec + MACScheme.prfSpec inpT.denote tagT.denote) α) := by
  induction p using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t mx ih =>
    simp only [Iface.liftP, simulateQ_query_bind, prfIface, monadLift_bind] at ih ⊢
    exact bind_congr ih

omit [DecidableEq Pt] in
@[simp] theorem saltRedIface_liftP {α : Type} (p : ProbComp α) :
    (SaltIface).liftP p =
      (liftM p : OracleComp (unifSpec + MACScheme.prfSpec Salt32 DerivedMessageKeys) α) :=
  prfIface_liftP (S := SWSig) (.base .salt) (.base .msgKey) p

omit [DecidableEq Pt] in
@[simp] theorem eval_ret {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {u : Ty S} (e : Expr O Γ u) (ρ : Env Γ) :
    (Comp.ret (I := I) e).eval ρ = pure (e.eval ρ) := rfl

omit [DecidableEq Pt] in
@[simp] theorem eval_bind {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {t u : Ty S} (c : Comp O I Γ t) (k : Comp O I (t :: Γ) u) (ρ : Env Γ) :
    (Comp.bind c k).eval ρ = (c.eval ρ >>= fun x => k.eval (.cons x ρ)) := rfl

omit [DecidableEq Pt] in
@[simp high] theorem eval_bind_ret {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} {Γ : List (Ty S)} {t u : Ty S}
    (e : Expr O Γ t) (k : Comp O I (t :: Γ) u) (ρ : Env Γ) :
    (Comp.bind (.ret e) k).eval ρ = k.eval (.cons (e.eval ρ) ρ) :=
  pure_bind (e.eval ρ) (fun x => k.eval (.cons x ρ))

omit [DecidableEq Pt] in
@[simp] theorem eval_ite {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {u : Ty S} (b : Expr O Γ .bool) (c d : Comp O I Γ u) (ρ : Env Γ) :
    (Comp.ite b c d).eval ρ = (if b.eval ρ = true then c.eval ρ else d.eval ρ) := rfl

omit [DecidableEq Pt] in
@[simp] theorem eval_caseOpt {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {a u : Ty S}
    (e : Expr O Γ (.opt a)) (n : Comp O I Γ u) (s : Comp O I (a :: Γ) u) (ρ : Env Γ) :
    (Comp.caseOpt e n s).eval ρ =
      match e.eval ρ with
      | Option.none => n.eval ρ
      | Option.some x => s.eval (.cons x ρ) := rfl

omit [DecidableEq Pt] in
@[simp] theorem eval_iter {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {t : Ty S}
    (n : ℕ) (e : Expr O Γ t) (body : Comp O I (t :: Γ) t) (ρ : Env Γ) :
    (Comp.iter n e body).eval ρ = iterM (fun a => body.eval (.cons a ρ)) n (e.eval ρ) := rfl

@[simp] theorem sample_saltRed_bool {Γ : List SWT} (ρ : Env Γ) :
    (sampleSaltBoolC C codec ℓ encT idOf kAEAD kIdeal).eval ρ =
      (liftM ($ᵗ Bool : ProbComp Bool) :
        OracleComp (unifSpec + MACScheme.prfSpec Salt32 DerivedMessageKeys) Bool) := by
  dsimp only [sampleSaltBoolC, Comp.eval]
  exact saltRedIface_liftP C codec ℓ encT kIdeal ($ᵗ Bool)

@[simp] theorem sample_saltRed_ideal {Γ : List SWT}
    (e : Expr SWOps Γ (slotAdTy Pt ℓ)) (ρ : Env Γ) :
    (sampleSaltIdealC C codec ℓ encT idOf kAEAD kIdeal e).eval ρ =
      (liftM (lIdeal C codec ℓ encT (e.eval ρ)) :
        OracleComp (unifSpec + MACScheme.prfSpec Salt32 DerivedMessageKeys) LibsignalCiphertextWithSalt32) := by
  dsimp only [sampleSaltIdealC, Comp.eval]
  exact saltRedIface_liftP C codec ℓ encT kIdeal (lIdeal C codec ℓ encT (e.eval ρ))

@[simp] theorem query_saltRed {Γ : List SWT}
    (e : Expr SWOps Γ (.base .salt)) (ρ : Env Γ) :
    (querySaltPrfC C codec ℓ encT idOf kAEAD kIdeal e).eval ρ =
      MACScheme.evalQuery (Input := Salt32) (Tag := DerivedMessageKeys) (e.eval ρ) := by
  dsimp only [querySaltPrfC, Comp.eval, MACScheme.evalQuery]
  exact id_map _

omit [DecidableEq Pt] in
theorem wireIface_liftP {S : Sig} (adT hdrT msgT msg'T rawT tagT : Ty S)
    (toBytes : rawT.denote → List (BitVec 8)) (ofBytes : List (BitVec 8) → rawT.denote)
    {α : Type} (p : ProbComp α) :
    (wireIface adT hdrT msgT msg'T rawT tagT toBytes ofBytes).liftP p =
      (liftM p :
        OracleComp (unifSpec +
          WireAEAD.wireSpec adT.denote hdrT.denote msgT.denote msg'T.denote tagT.denote) α) := by
  induction p using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t mx ih =>
    simp only [Iface.liftP, simulateQ_query_bind, monadLift_bind] at ih ⊢
    exact bind_congr ih

omit [DecidableEq Pt] in
@[simp] theorem wireRedIface_liftP {α : Type} (p : ProbComp α) :
    (WireIface).liftP p = (liftM p : OracleComp (LibsignalWireOracleSpec ℓ) α) :=
  wireIface_liftP (S := SWSig) (.base .idKeys) (.base .sigHdr) (.base .plain) (.base .rawBytes)
    (.base .rawBytes) (.base .macTag) id id p

@[simp] theorem sample_wireRed_bool {Γ : List SWT} (ρ : Env Γ) :
    (sampleWireBoolC C codec ℓ encT idOf kAEAD).eval ρ =
      (liftM ($ᵗ Bool : ProbComp Bool) : OracleComp (LibsignalWireOracleSpec ℓ) Bool) := by
  dsimp only [sampleWireBoolC, Comp.eval]
  exact wireRedIface_liftP ℓ ($ᵗ Bool)

@[simp] theorem query_wireRed_enc {Γ : List SWT}
    (e : Expr SWOps Γ (.prod (.base .idKeys) (.prod (.base .sigHdr) (.base .plain))))
    (ρ : Env Γ) :
    (queryWireEncC C codec ℓ encT idOf kAEAD e).eval ρ =
      query (spec := LibsignalWireOracleSpec ℓ)
        (.inr (.inl ((e.eval ρ).1, (e.eval ρ).2.1, (e.eval ρ).2.2))) := by
  dsimp only [queryWireEncC, Comp.eval]
  have hdec : Option.map (fun x : List (BitVec 8) × BitVec 64 => (x.1, x.2)) = id := by
    funext r; cases r <;> rfl
  change Option.map (fun x : List (BitVec 8) × BitVec 64 => (x.1, x.2)) <$>
      query (spec := LibsignalWireOracleSpec ℓ)
        (.inr (.inl ((e.eval ρ).1, (e.eval ρ).2.1, (e.eval ρ).2.2))) = _
  rw [hdec, id_map]

@[simp] theorem query_wireRed_dec {Γ : List SWT}
    (e : Expr SWOps Γ (.prod (.base .idKeys) (wireTagTy Pt ℓ))) (ρ : Env Γ) :
    (queryWireDecC C codec ℓ encT idOf kAEAD e).eval ρ =
      query (spec := LibsignalWireOracleSpec ℓ) (.inr (.inr ((e.eval ρ).1, (e.eval ρ).2))) := by
  dsimp only [queryWireDecC, Comp.eval]
  exact id_map _

omit [DecidableEq Pt] in
theorem otccaIface_liftP {S : Sig} (adT msgT ctT : Ty S)
    (ideal : adT.denote → ProbComp ctT.denote) (kI : ℕ) {α : Type} (p : ProbComp α) :
    (otccaIface adT msgT ctT ideal kI).liftP p =
      (liftM p :
        OracleComp (unifSpec + AEADScheme.otccaSpec adT.denote msgT.denote ctT.denote) α) := by
  induction p using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t mx ih =>
    simp only [Iface.liftP, simulateQ_query_bind, otccaIface, monadLift_bind] at ih ⊢
    exact bind_congr ih

omit [DecidableEq Pt] in
@[simp] theorem slotOtccaIface_liftP {α : Type} (p : ProbComp α) :
    (SlotIface).liftP p =
      (liftM p : OracleComp (FSAEAD.Thm5.IndexedOtccaSpec (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) α) :=
  otccaIface_liftP (S := SWSig) (slotAdTy Pt ℓ) (.base .plain) (lctTy Pt ℓ)
    (lIdeal C codec ℓ encT) kIdeal p

@[simp] theorem sample_slotOtcca_ideal {Γ : List SWT}
    (e : Expr SWOps Γ (slotAdTy Pt ℓ)) (ρ : Env Γ) :
    (sampleSlotIdealC C codec ℓ encT idOf kAEAD kIdeal e).eval ρ =
      (liftM (lIdeal C codec ℓ encT (e.eval ρ)) :
        OracleComp (FSAEAD.Thm5.IndexedOtccaSpec (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) LibsignalCiphertextWithSalt32) := by
  dsimp only [sampleSlotIdealC, Comp.eval]
  exact slotOtccaIface_liftP C codec ℓ encT kIdeal (lIdeal C codec ℓ encT (e.eval ρ))

@[simp] theorem sample_slotOtcca_seed {Γ : List SWT} (ρ : Env Γ) :
    (sampleSlotSeedC C codec ℓ encT idOf kAEAD kIdeal).eval ρ =
      (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
        OracleComp (FSAEAD.Thm5.IndexedOtccaSpec (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (BitVec 256)) := by
  dsimp only [sampleSlotSeedC, Comp.eval]
  exact slotOtccaIface_liftP C codec ℓ encT kIdeal ($ᵗ (BitVec 256))

@[simp] theorem sample_slotOtcca_msgKey {Γ : List SWT} (ρ : Env Γ) :
    (sampleSlotMsgKeyC C codec ℓ encT idOf kAEAD kIdeal).eval ρ =
      (liftM ($ᵗ DerivedMessageKeys : ProbComp DerivedMessageKeys) :
        OracleComp (FSAEAD.Thm5.IndexedOtccaSpec (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) DerivedMessageKeys) := by
  dsimp only [sampleSlotMsgKeyC, Comp.eval]
  exact slotOtccaIface_liftP C codec ℓ encT kIdeal ($ᵗ DerivedMessageKeys)

@[simp] theorem query_slotOtcca_enc_v0 {Γ : List SWT}
    (x : (Ty.prod (S := SWSig) (slotAdTy Pt ℓ) (.base .plain)).denote) (ρ : Env Γ) :
    (querySlotEncC C codec ℓ encT idOf kAEAD kIdeal (.var .zero)).eval (.cons x ρ) =
      query (spec := FSAEAD.Thm5.IndexedOtccaSpec (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)
        (.inr (.inl x)) := by
  dsimp only [querySlotEncC, Comp.eval, Expr.eval, Env.get]
  exact id_map _

@[simp] theorem query_slotOtcca_dec_v0 {Γ : List SWT}
    (x : (Ty.prod (S := SWSig) (slotAdTy Pt ℓ) (lctTy Pt ℓ)).denote) (ρ : Env Γ) :
    (querySlotDecC C codec ℓ encT idOf kAEAD kIdeal (.var .zero)).eval (.cons x ρ) =
      query (spec := FSAEAD.Thm5.IndexedOtccaSpec (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)
        (.inr (.inr x)) := by
  dsimp only [querySlotDecC, Comp.eval, Expr.eval, Env.get]
  exact id_map _

omit [DecidableEq Pt] in
theorem run_lift_map_enc {ι : Type} {T : OracleSpec ι} {α σ₁ σ₂ : Type}
    (oa : OracleComp T α) (enc : σ₂ → σ₁) (s : σ₂) :
    (StateT.lift oa).run (enc s) = Prod.map id enc <$> (StateT.lift oa).run s := by
  simp only [StateT.run_lift, Prod.map, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind, id_eq]

@[reducible] def slotQueryTy : SWT :=
  .sum (.prod (slotAdTy Pt ℓ) (.base .plain)) (.prod (slotAdTy Pt ℓ) (lctTy Pt ℓ))

@[reducible] def slotRdecEnc (r : (slotReplyTy (Pt := Pt) ℓ).denote) : Option LibsignalCiphertextWithSalt32 :=
  Sum.casesOn r id (fun _ => none)

@[reducible] def slotRdecDec (r : (slotReplyTy (Pt := Pt) ℓ).denote) : Option (Plain ℓ) :=
  Sum.casesOn r (fun _ => none) id

theorem handlerImpl_slotOtcca_enc {ι : Type} {T : OracleSpec ι} {I : Iface SWSig T}
    {σ : SWT}
    (encB : ∀ {Γ}, Comp SWOps I (.prod (slotAdTy Pt ℓ) (.base .plain) :: σ :: Γ)
      (.prod (slotReplyTy (Pt := Pt) ℓ) σ))
    (decB : ∀ {Γ}, Comp SWOps I (.prod (slotAdTy Pt ℓ) (lctTy Pt ℓ) :: σ :: Γ)
      (.prod (slotReplyTy (Pt := Pt) ℓ) σ))
    (a : ℕ × (Header Pt × LibsignalMsgPublicPart)) (m : Plain ℓ) (s : σ.denote) :
    (handlerImpl (C := SlotCodec) (.caseSum .v1 encB decB) (.inr (.inl ⟨a, m⟩))).run s =
      (do
        let p ← (encB (Γ := [slotQueryTy (Pt := Pt) ℓ])).eval
          (.cons (a, m) (.cons s (.cons (t := slotQueryTy (Pt := Pt) ℓ) (Sum.inl (a, m)) .nil)))
        pure (slotRdecEnc ℓ p.1, p.2)) := by
  dsimp only [handlerImpl, slotOtccaCodec, otccaCodec, Comp.eval, Expr.v1, Expr.eval, Env.get,
    StateT.run_mk]
  refine bind_congr fun p => ?_
  rcases p with ⟨c | m', s'⟩ <;> rfl

theorem handlerImpl_slotOtcca_dec {ι : Type} {T : OracleSpec ι} {I : Iface SWSig T}
    {σ : SWT}
    (encB : ∀ {Γ}, Comp SWOps I (.prod (slotAdTy Pt ℓ) (.base .plain) :: σ :: Γ)
      (.prod (slotReplyTy (Pt := Pt) ℓ) σ))
    (decB : ∀ {Γ}, Comp SWOps I (.prod (slotAdTy Pt ℓ) (lctTy Pt ℓ) :: σ :: Γ)
      (.prod (slotReplyTy (Pt := Pt) ℓ) σ))
    (a : ℕ × (Header Pt × LibsignalMsgPublicPart)) (e : LibsignalCiphertextWithSalt32) (s : σ.denote) :
    (handlerImpl (C := SlotCodec) (.caseSum .v1 encB decB) (.inr (.inr ⟨a, e⟩))).run s =
      (do
        let p ← (decB (Γ := [slotQueryTy (Pt := Pt) ℓ])).eval
          (.cons (a, e) (.cons s (.cons (t := slotQueryTy (Pt := Pt) ℓ) (Sum.inr (a, e)) .nil)))
        pure (slotRdecDec ℓ p.1, p.2)) := by
  dsimp only [handlerImpl, slotOtccaCodec, otccaCodec, Comp.eval, Expr.v1, Expr.eval, Env.get,
    StateT.run_mk]
  refine bind_congr fun p => ?_
  rcases p with ⟨c | m', s'⟩ <;> rfl

omit [DecidableEq Pt] in
@[simp] theorem decide_ne_salt (s₁ s₂ : Salt32) :
    decide (s₁ ≠ s₂) = !(s₁ == s₂) := by
  by_cases h : s₁ = s₂ <;> simp [h]

omit [DecidableEq Pt] in
@[simp] theorem cond_beq_bool (a b : Bool) :
    (if a = true then b else !b) = (a == b) := by
  cases a <;> cases b <;> rfl

@[simp] theorem orE_eval {Γ : List SWT} (a b : Expr SWOps Γ .bool) (ρ : Env Γ) :
    (orE C codec ℓ encT idOf kAEAD a b).eval ρ = (a.eval ρ || b.eval ρ) := by
  simp [orE, Expr.eval]

@[simp] theorem eqBoolE_eval {Γ : List SWT} (a b : Expr SWOps Γ .bool) (ρ : Env Γ) :
    (eqBoolE C codec ℓ encT idOf kAEAD a b).eval ρ = (a.eval ρ == b.eval ρ) := by
  simp [eqBoolE, Expr.eval]

@[simp] theorem leE_eval {Γ : List SWT} (a b : Expr SWOps Γ .nat) (ρ : Env Γ) :
    (leE C codec ℓ encT idOf kAEAD a b).eval ρ = decide (a.eval ρ ≤ b.eval ρ) := by
  have h : ∀ x y : ℕ, (!decide (y < x)) = decide (x ≤ y) := fun x y => by
    by_cases hxy : x ≤ y
    · have hlt : ¬ y < x := by omega
      simp [hxy, hlt]
    · have hlt : y < x := by omega
      simp [hxy, hlt]
  exact h (a.eval ρ) (b.eval ρ)

@[simp] theorem isSomeE_eval {Γ : List SWT} {t : SWT} (e : Expr SWOps Γ (.opt t)) (ρ : Env Γ) :
    (isSomeE C codec ℓ encT idOf kAEAD e).eval ρ = (e.eval ρ).isSome := by
  simp only [isSomeE, Expr.eval]
  cases e.eval ρ <;> rfl

@[simp] theorem encKE_eval {Γ : List SWT}
    (mk : Expr SWOps Γ (.base .msgKey))
    (a : Expr SWOps Γ (slotAdTy Pt ℓ))
    (m : Expr SWOps Γ (.base .plain)) (ρ : Env Γ) :
    (encKE C codec ℓ encT idOf kAEAD mk a m).eval ρ =
      (lAeadK C codec ℓ encT idOf).enc (mk.eval ρ)
        (((a.eval ρ).1, (a.eval ρ).2.1), (a.eval ρ).2.2) (m.eval ρ) := rfl

@[simp] theorem decKE_eval {Γ : List SWT}
    (mk : Expr SWOps Γ (.base .msgKey))
    (a : Expr SWOps Γ (slotAdTy Pt ℓ))
    (e : Expr SWOps Γ (lctTy Pt ℓ)) (ρ : Env Γ) :
    (decKE C codec ℓ encT idOf kAEAD mk a e).eval ρ =
      (lAeadK C codec ℓ encT idOf).dec (mk.eval ρ)
        (((a.eval ρ).1, (a.eval ρ).2.1), (a.eval ρ).2.2) (e.eval ρ) := rfl

@[simp] theorem encRE_eval {Γ : List SWT}
    (seed : Expr SWOps Γ (.base .seed))
    (a : Expr SWOps Γ (slotAdTy Pt ℓ))
    (m : Expr SWOps Γ (.base .plain)) (ρ : Env Γ) :
    (encRE C codec ℓ encT idOf kAEAD seed a m).eval ρ =
      (lAeadR C codec ℓ encT idOf).enc (seed.eval ρ) (a.eval ρ) (m.eval ρ) := rfl

@[simp] theorem decRE_eval {Γ : List SWT}
    (seed : Expr SWOps Γ (.base .seed))
    (a : Expr SWOps Γ (slotAdTy Pt ℓ))
    (e : Expr SWOps Γ (lctTy Pt ℓ)) (ρ : Env Γ) :
    (decRE C codec ℓ encT idOf kAEAD seed a e).eval ρ =
      (lAeadR C codec ℓ encT idOf).dec (seed.eval ρ) (a.eval ρ) (e.eval ρ) := rfl

@[simp] theorem saltOfE_eval {Γ : List SWT} (a : Expr SWOps Γ (slotAdTy Pt ℓ)) (ρ : Env Γ) :
    (saltOfE C codec ℓ encT idOf kAEAD a).eval ρ = (a.eval ρ).2.2.salt := rfl

@[simp] theorem eqADE_eval {Γ : List SWT} (a₁ a₂ : Expr SWOps Γ (slotAdTy Pt ℓ)) (ρ : Env Γ) :
    (eqADE C codec ℓ encT idOf kAEAD a₁ a₂).eval ρ = (a₁.eval ρ == a₂.eval ρ) := by
  change decide (a₁.eval ρ = a₂.eval ρ) = (a₁.eval ρ == a₂.eval ρ)
  by_cases h : a₁.eval ρ = a₂.eval ρ <;> simp [h]

@[simp] theorem eqCE_eval {Γ : List SWT} (e₁ e₂ : Expr SWOps Γ (lctTy Pt ℓ)) (ρ : Env Γ) :
    (eqCE C codec ℓ encT idOf kAEAD e₁ e₂).eval ρ = (e₁.eval ρ == e₂.eval ρ) := by
  change decide (e₁.eval ρ = e₂.eval ρ) = (e₁.eval ρ == e₂.eval ρ)
  by_cases h : e₁.eval ρ = e₂.eval ρ <;> simp [h]

@[simp] theorem eqSaltE_eval {Γ : List SWT} (s₁ s₂ : Expr SWOps Γ (.base .salt)) (ρ : Env Γ) :
    (eqSaltE C codec ℓ encT idOf kAEAD s₁ s₂).eval ρ = (s₁.eval ρ == s₂.eval ρ) := rfl

@[simp] theorem idsOfE_eval {Γ : List SWT} (a : Expr SWOps Γ (slotAdTy Pt ℓ)) (ρ : Env Γ) :
    (idsOfE C codec ℓ encT idOf kAEAD a).eval ρ = lIds idOf (a.eval ρ).2.1.1 := rfl

@[simp] theorem hdrOfE_eval {Γ : List SWT} (a : Expr SWOps Γ (slotAdTy Pt ℓ)) (ρ : Env Γ) :
    (hdrOfE C codec ℓ encT idOf kAEAD a).eval ρ =
      lHeader encT (a.eval ρ).1 (a.eval ρ).2.1 (a.eval ρ).2.2 := rfl

@[simp] theorem eqHdrE_eval {Γ : List SWT} (h₁ h₂ : Expr SWOps Γ (.base .sigHdr)) (ρ : Env Γ) :
    (eqHdrE C codec ℓ encT idOf kAEAD h₁ h₂).eval ρ = (h₁.eval ρ == h₂.eval ρ) := rfl

@[simp] theorem fitPlainE_eval {Γ : List SWT} (m : Expr SWOps Γ (.base .rawBytes)) (ρ : Env Γ) :
    (fitPlainE C codec ℓ encT idOf kAEAD m).eval ρ = padOrTruncatePlain ℓ (m.eval ρ) := rfl

@[simp] theorem emptySaltSlotStE_eval {Γ : List SWT} (ρ : Env Γ) :
    (emptySaltSlotStE C codec ℓ encT idOf kAEAD).eval ρ = (none, []) := rfl

@[simp] theorem eqChalSomeE_v0_eval {Γ : List SWT}
    (chal : Expr SWOps (.prod (slotAdTy Pt ℓ) (lctTy Pt ℓ) :: Γ) (chalOptTy (Pt := Pt) ℓ))
    (ae : (ℕ × (Header Pt × LibsignalMsgPublicPart)) × LibsignalCiphertextWithSalt32) (ρ : Env Γ) :
    (eqChalSomeE C codec ℓ encT idOf kAEAD chal
      (.fst (.var (.succ .zero))) (.snd (.var (.succ .zero)))).eval (.cons ae ρ) =
      (chal.eval (.cons ae ρ) == some ae) := by
  simp only [eqChalSomeE, Expr.eval]
  cases chal.eval (.cons ae ρ) with
  | none => rfl
  | some p =>
    rcases p with ⟨a₀, e₀⟩
    rcases ae with ⟨a, e⟩
    simp only [eqADE_eval, eqCE_eval, Expr.v0, Expr.eval, Env.get]
    rfl

@[simp] theorem eqChalSomeE_v1_eval {t : SWT} {Γ : List SWT}
    (chal : Expr SWOps (t :: .prod (slotAdTy Pt ℓ) (lctTy Pt ℓ) :: Γ) (chalOptTy (Pt := Pt) ℓ))
    (x : t.denote) (ae : (ℕ × (Header Pt × LibsignalMsgPublicPart)) × LibsignalCiphertextWithSalt32) (ρ : Env Γ) :
    (eqChalSomeE C codec ℓ encT idOf kAEAD chal
      (.fst .v2) (.snd .v2)).eval
      (.cons x (.cons ae ρ)) =
      (chal.eval (.cons x (.cons ae ρ)) == some ae) := by
  simp only [eqChalSomeE, Expr.eval]
  cases chal.eval (.cons x (.cons ae ρ)) with
  | none => rfl
  | some p =>
    rcases p with ⟨a₀, e₀⟩
    rcases ae with ⟨a, e⟩
    simp only [eqADE_eval, eqCE_eval, Expr.v0, Expr.v2, Expr.eval, Env.get]
    rfl

@[simp] theorem isSlotChalSaltE_v1_eval {t : SWT} {Γ : List SWT}
    (chal : Expr SWOps (t :: .prod (slotAdTy Pt ℓ) (lctTy Pt ℓ) :: Γ) (chalOptTy (Pt := Pt) ℓ))
    (x : t.denote) (ae : (ℕ × (Header Pt × LibsignalMsgPublicPart)) × LibsignalCiphertextWithSalt32) (ρ : Env Γ) :
    (isSlotChalSaltE C codec ℓ encT idOf kAEAD chal
      (saltOfE C codec ℓ encT idOf kAEAD (.fst .v2))).eval
      (.cons x (.cons ae ρ)) =
      isSlotChalSalt (chal.eval (.cons x (.cons ae ρ))) ae.1.2.2.salt := by
  simp only [isSlotChalSaltE, isSlotChalSalt, Expr.eval]
  cases chal.eval (.cons x (.cons ae ρ)) with
  | none => rfl
  | some p =>
    rcases p with ⟨a₀, e₀⟩
    simp only [eqSaltE_eval, saltOfE_eval, Expr.v0, Expr.v2, Expr.eval, Env.get]

/-! ## `lSaltRedProg` -/

def lSaltRedImpl (b : Bool) :
    QueryImpl (unifSpec + AEADScheme.otccaSpec (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32)
      (StateT (Option ((ℕ × (Header Pt × LibsignalMsgPublicPart)) × LibsignalCiphertextWithSalt32))
        (OracleComp (unifSpec + MACScheme.prfSpec Salt32 DerivedMessageKeys)))
  | .inl n => StateT.lift (query (spec := unifSpec + MACScheme.prfSpec Salt32 DerivedMessageKeys) (.inl n))
  | .inr (.inl ⟨a, m⟩) => do
    if (← get).isSome then return none
    let mk ← StateT.lift (MACScheme.evalQuery (Input := Salt32) (Tag := DerivedMessageKeys) a.2.2.salt)
    let e ← if b then StateT.lift (liftM (lIdeal C codec ℓ encT a))
      else pure ((lAeadK C codec ℓ encT idOf).enc mk ((a.1, a.2.1), a.2.2) m)
    set (some (a, e))
    return some e
  | .inr (.inr ⟨a, e⟩) => do
    if b || (← get) == some (a, e) || e.2 ≠ a.2.2.salt then return none
    let mk ← StateT.lift (MACScheme.evalQuery (Input := Salt32) (Tag := DerivedMessageKeys) a.2.2.salt)
    return (lAeadK C codec ℓ encT idOf).dec mk ((a.1, a.2.1), a.2.2) e

theorem lSaltRedProg_step_eval (b : Bool)
    (t : (unifSpec + AEADScheme.otccaSpec (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32).Domain)
    (chal : Option ((ℕ × (Header Pt × LibsignalMsgPublicPart)) × LibsignalCiphertextWithSalt32)) :
    ((lSaltRedProg C codec ℓ encT idOf kAEAD kIdeal).impl t).run (b, chal) =
      Prod.map id (fun c => (b, c)) <$>
        (lSaltRedImpl C codec ℓ encT idOf b t).run chal := by
  rcases t with n | (⟨a, m⟩ | ⟨a, e⟩)
  · exact run_lift_map_enc _ (fun c => (b, c)) chal
  · dsimp only [CostedReduction.impl, lSaltRedProg]
    rw [handlerImpl_slotOtcca_enc]
    dsimp only [lSaltEncC]
    cases chal with
    | some p =>
      simp [lSaltRedImpl, isSomeE_eval, Expr.v1, Expr.eval, Env.get, Prod.map]
    | none =>
      cases b <;>
        simp only [lSaltRedImpl, eval_ite, eval_bind, eval_ret, query_saltRed,
          sample_saltRed_ideal, isSomeE_eval, saltOfE_eval, encKE_eval,
          Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.eval, Env.get,
          Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_set, StateT.run_pure,
          pure_bind, bind_assoc, map_eq_bind_pure_comp, Function.comp_def,
          Prod.map, id_eq]
  · dsimp only [CostedReduction.impl, lSaltRedProg]
    rw [handlerImpl_slotOtcca_dec]
    dsimp only [lSaltDecC]
    by_cases hcond : ((b || chal == some (a, e)) || !(e.2 == a.2.2.salt)) = true
    · simp only [lSaltRedImpl, eval_ite, eval_ret, orE_eval, eqChalSomeE_v0_eval, eqSaltE_eval,
        saltOfE_eval, Expr.v0, Expr.v1, Expr.eval, Env.get, decide_ne_salt, hcond, ↓reduceIte,
        StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, map_pure,
        Prod.map, id_eq]
    · simp only [lSaltRedImpl, eval_ite, eval_bind, eval_ret, query_saltRed, orE_eval,
        eqChalSomeE_v0_eval, eqSaltE_eval, saltOfE_eval, decKE_eval,
        Expr.v0, Expr.v1, Expr.v2, Expr.eval, Env.get, decide_ne_salt, hcond, Bool.false_eq_true,
        ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_lift, StateT.run_pure,
        pure_bind, bind_assoc, map_eq_bind_pure_comp, Function.comp_def,
        Prod.map, id_eq]

omit [DecidableEq Pt] in
theorem simulateQ_run_enc {ι κ : Type} {T : OracleSpec.{0, 0} ι} {spec : OracleSpec.{0, 0} κ}
    {σ₁ σ₂ : Type} (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp T)))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp T))) (enc : σ₂ → σ₁)
    (hstep : ∀ t s, (impl₁ t).run (enc s) = Prod.map id enc <$> (impl₂ t).run s) :
    ∀ {α : Type} (oa : OracleComp spec α) (s : σ₂),
      (simulateQ impl₁ oa).run (enc s) = Prod.map id enc <$> (simulateQ impl₂ oa).run s := by
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure x => intro s; simp [Prod.map]
  | query_bind t mx ih =>
    intro s
    simp only [simulateQ_query_bind, StateT.run_bind, OracleQuery.input_query,
      OracleQuery.cont_query, map_bind]
    change (impl₁ t).run (enc s) >>= _ = (impl₂ t).run s >>= _
    rw [hstep t s, bind_map_left]
    refine bind_congr fun z => ih z.1 z.2

/-- On every OT-CCA adversary `B`, `lSaltRedProg` evaluates to `lSaltRed`. -/
theorem lSaltRedProg_eval
    (B : AEADScheme.OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32) :
    (lSaltRedProg C codec ℓ encT idOf kAEAD kIdeal).eval (fun _ => B) () =
      lSaltRed C codec ℓ encT idOf B := by
  have hsim := fun (b : Bool) =>
    simulateQ_run_enc
      ((lSaltRedProg C codec ℓ encT idOf kAEAD kIdeal).impl)
      (lSaltRedImpl C codec ℓ encT idOf b)
      (fun c => (b, c))
      (lSaltRedProg_step_eval C codec ℓ encT idOf kAEAD kIdeal b)
      B none
  dsimp only [CostedReduction.eval, lSaltRed, StateT.run']
  simp only [lSaltRedProg, lSaltInitC, eval_bind, eval_ret, sample_saltRed_bool,
    Expr.v0, Expr.eval, Env.get, bind_assoc, pure_bind]
  refine bind_congr fun b => ?_
  change (do
      let q ← (simulateQ (lSaltRedProg C codec ℓ encT idOf kAEAD kIdeal).impl B).run (b, none)
      (lSaltRedProg C codec ℓ encT idOf kAEAD kIdeal).finish.eval
        (.cons q.2 (.cons q.1 .nil))) = _
  rw [hsim b, bind_map_left, bind_map_left]
  refine bind_congr fun z => ?_
  simp [lSaltRedProg, lSaltFinishC, Expr.v0, Expr.v1, Expr.eval, Env.get, Prod.map]

/-! ## `lWireRedProg` -/

abbrev WRedSt := List Salt32 × List (Salt32 × DerivedMessageKeys) × Bool × Bool

def encSalts : List Salt32 → List (Salt32 × ℕ) :=
  List.foldl (fun acc s => (s, acc.length) :: acc) []

@[simp] def encWireSt (st : WRedSt) : (wireStTy (Pt := Pt) ℓ).denote :=
  (encSalts st.1, (st.2.2.1, st.2.2.2))

omit [DecidableEq Pt] in
theorem foldl_encSalts_length :
    ∀ (xs : List Salt32) (acc : List (Salt32 × ℕ)),
      (xs.foldl (fun a s => (s, a.length) :: a) acc).length = acc.length + xs.length
  | [], acc => by simp
  | s :: xs, acc => by
    simp only [List.foldl_cons, foldl_encSalts_length xs ((s, acc.length) :: acc),
      List.length_cons]
    omega

@[simp] theorem encSalts_nil : encSalts [] = [] := rfl

omit [DecidableEq Pt] in
@[simp] theorem encSalts_length (xs : List Salt32) : (encSalts xs).length = xs.length := by
  simpa [encSalts] using foldl_encSalts_length xs []

omit [DecidableEq Pt] in
@[simp] theorem encSalts_append_singleton (xs : List Salt32) (salt : Salt32) :
    encSalts (xs ++ [salt]) = (salt, xs.length) :: encSalts xs := by
  simp only [encSalts, List.foldl_append, List.foldl_cons, List.foldl_nil,
    foldl_encSalts_length, List.length_nil, Nat.zero_add]

omit [DecidableEq Pt] in
theorem idxOf?_append_singleton_of_none :
    ∀ (xs : List Salt32) (salt x : Salt32),
      xs.idxOf? salt = none →
      (xs ++ [salt]).idxOf? x = if salt == x then some xs.length else xs.idxOf? x
  | [], salt, x, _ => by
    simp only [List.nil_append, List.idxOf?_cons, List.idxOf?_nil, List.length_nil, Option.map_none]
  | y :: xs, salt, x, hnone => by
    simp only [List.idxOf?_cons] at hnone
    by_cases hys : y = salt
    · subst hys; simp at hnone
    · have hys' : (y == salt) = false := by simp [hys]
      simp only [hys', Bool.false_eq_true, ↓reduceIte, Option.map_eq_none_iff] at hnone
      simp only [List.cons_append, List.idxOf?_cons, List.length_cons,
        idxOf?_append_singleton_of_none xs salt x hnone]
      by_cases hyx : y = x
      · subst hyx
        have hsx : (salt == y) = false := by simp [Ne.symm hys]
        simp [hsx]
      · have hyx' : (y == x) = false := by simp [hyx]
        simp only [hyx', Bool.false_eq_true, ↓reduceIte]
        cases salt == x <;> rfl

/-- Query-budget invariant on `WRedSt` after `n` game queries. -/
def WireInv (n : ℕ) (st : WRedSt) : Prop :=
  st.1.length ≤ n ∧
    ∀ x, (encSalts st.1).find? (fun e => e.1 == x) = (st.1.idxOf? x).map (x, ·)

theorem WireInv.init : WireInv 0 ([], [], false, false) :=
  ⟨le_rfl, fun _ => rfl⟩

omit [DecidableEq Pt] in
theorem WireInv.append_of_none {n : ℕ} {st : WRedSt} (hI : WireInv n st)
    {salt : Salt32} (hnone : st.1.idxOf? salt = none) (ab de : Bool) :
    WireInv (n + 1) (st.1 ++ [salt], st.2.1, ab, de) := by
  refine ⟨by simp [hI.1], fun x => ?_⟩
  rw [encSalts_append_singleton, List.find?_cons,
    idxOf?_append_singleton_of_none st.1 salt x hnone]
  by_cases hsx : salt = x
  · subst hsx; simp
  · have hsx' : (salt == x) = false := by simp [hsx]
    simp [hsx', hI.2 x]

omit [DecidableEq Pt] in
theorem WireInv.preserve_salts {n : ℕ} {st : WRedSt} (hI : WireInv n st) (ab de : Bool) :
    WireInv (n + 1) (st.1, st.2.1, ab, de) :=
  ⟨Nat.le_succ_of_le hI.1, hI.2⟩

theorem wireSlotE_eval (q : ℕ) (st : WRedSt) {n : ℕ} (hI : WireInv n st) (hq : n < q)
    (salt : Salt32) {Γ : List SWT} (ρ : Env Γ) :
    (wireSlotE C codec ℓ encT idOf kAEAD q).eval
      (.cons salt (.cons (encSalts st.1) ρ)) =
    match st.1.idxOf? salt with
    | some idx => (idx, encSalts st.1)
    | none => (st.1.length, encSalts (st.1 ++ [salt])) := by
  have hlen : st.1.length ≤ n := hI.1
  have htake : (encSalts st.1).take q = encSalts st.1 :=
    List.take_of_length_le (by rw [encSalts_length]; omega)
  simp only [wireSlotE, eqSaltE_eval, Expr.v0, Expr.v1, Expr.eval, Env.get, htake, hI.2 salt]
  cases st.1.idxOf? salt with
  | some idx =>
    simp [Option.map, Expr.v2, Expr.eval, Env.get]
  | none =>
    simp only [Option.map]
    rw [encSalts_length st.1, encSalts_append_singleton st.1 salt]

def wSlot (salt : Salt32) : StateT WRedSt (OracleComp (LibsignalWireOracleSpec ℓ)) ℕ := do
  let st ← get
  match st.1.idxOf? salt with
  | some n => return n
  | none => set (st.1 ++ [salt], st.2.1, st.2.2.1, st.2.2.2); return st.1.length

def wRedImpl (j : ℕ) :
    QueryImpl (unifSpec + AEADScheme.otccaSpec (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32)
      (StateT WRedSt (OracleComp (LibsignalWireOracleSpec ℓ))) := fun q =>
  let _ := (C, codec)
  match q with
  | .inl n => StateT.lift (query (spec := LibsignalWireOracleSpec ℓ) (.inl n))
  | .inr (.inl ⟨a, m⟩) => do
    if (← get).2.2.2 then return none
    let n ← wSlot ℓ a.2.2.salt
    modify fun st => (st.1, st.2.1, st.2.2.1, true)
    if n ≠ j then
      modify fun st => (st.1, st.2.1, true, st.2.2.2)
      return none
    let r ← StateT.lift (query (spec := LibsignalWireOracleSpec ℓ)
      (.inr (.inl (lIds idOf a.2.1.1, lHeader encT a.1 a.2.1 a.2.2, m))))
    return r.map fun w => (w, a.2.2.salt)
  | .inr (.inr ⟨a, e⟩) => do
    if !(← get).2.2.2 || e.2 ≠ a.2.2.salt then return none
    let n ← wSlot ℓ a.2.2.salt
    if n = j then
      let r ← StateT.lift (query (spec := LibsignalWireOracleSpec ℓ) (.inr (.inr (lIds idOf a.2.1.1, e.1))))
      return match r with
        | none => none
        | some (h, m) => if h = lHeader encT a.1 a.2.1 a.2.2 then some (padOrTruncatePlain ℓ m) else none
    else
      return none

theorem lWireRedProg_step_eval (j q : ℕ)
    (t : (unifSpec + AEADScheme.otccaSpec (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32).Domain)
    (st : WRedSt) (n : ℕ) (hI : WireInv n st)
    (hroom : t.isRight = true → n < q) :
    (((lWireRedProg C codec ℓ encT idOf kAEAD j q).impl t).run (encWireSt ℓ st) =
      Prod.map id (encWireSt ℓ) <$> (wRedImpl C codec ℓ encT idOf j t).run st) ∧
    (∀ z ∈ support ((wRedImpl C codec ℓ encT idOf j t).run st),
      WireInv (if t.isRight = true then n + 1 else n) z.2) := by
  rcases t with m | (⟨a, msg⟩ | ⟨a, e⟩)
  · refine ⟨run_lift_map_enc _ (encWireSt ℓ) st, ?_⟩
    intro z hz
    simp only [wRedImpl, StateT.run_lift, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨u, -, rfl⟩ := hz
    simpa using hI
  · have hq : n < q := hroom rfl
    dsimp only [CostedReduction.impl, lWireRedProg]
    rw [handlerImpl_slotOtcca_enc]
    dsimp only [lWireEncC]
    by_cases hde : st.2.2.2 = true
    · refine ⟨by simp [wRedImpl, encWireSt, Expr.v1, Expr.eval, Env.get, hde, Prod.map], ?_⟩
      intro z hz
      simp only [wRedImpl, StateT.run_bind, StateT.run_get, pure_bind, hde, ↓reduceIte,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hI.preserve_salts st.2.2.1 st.2.2.2
    · simp only [wRedImpl, wSlot, encWireSt, eval_ite, eval_bind_ret, saltOfE_eval,
        Expr.v0, Expr.v1, Expr.eval, Env.get, StateT.run_bind, StateT.run_get, pure_bind,
        hde, Bool.false_eq_true, ↓reduceIte]
      rw [wireSlotE_eval C codec ℓ encT idOf kAEAD q st hI hq a.2.2.salt]
      cases hidx : st.1.idxOf? a.2.2.salt with
      | some idx =>
        by_cases hnj : idx = j
        · subst hnj
          refine ⟨?_, ?_⟩
          · simp only [eval_bind, eval_ret, query_wireRed_enc, idsOfE_eval, hdrOfE_eval,
              Expr.v3, Expr.v5, Expr.eval, Env.get,
              decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ne_eq,
              not_true_eq_false, StateT.run_pure, StateT.run_bind, StateT.run_modify,
              StateT.run_lift, pure_bind, bind_assoc, map_eq_bind_pure_comp, Function.comp_def,
              encWireSt, Prod.map, id_eq]
            refine bind_congr fun r => ?_
            cases r <;> rfl
          · intro z hz
            simp only [StateT.run_pure, StateT.run_bind, StateT.run_modify, StateT.run_lift,
              pure_bind, bind_assoc, ne_eq, not_true_eq_false, ↓reduceIte,
              mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
            obtain ⟨r, -, rfl⟩ := hz
            exact hI.preserve_salts st.2.2.1 true
        · refine ⟨by simp [Expr.eval, Env.get, encWireSt, hnj, Prod.map], ?_⟩
          intro z hz
          simp only [StateT.run_pure, StateT.run_bind, StateT.run_modify, pure_bind,
            ne_eq, hnj, not_false_eq_true, ↓reduceIte,
            support_pure, Set.mem_singleton_iff] at hz
          subst hz
          exact hI.preserve_salts true true
      | none =>
        by_cases hnj : st.1.length = j
        · subst hnj
          refine ⟨?_, ?_⟩
          · simp only [eval_bind, eval_ret, query_wireRed_enc, idsOfE_eval, hdrOfE_eval,
              Expr.v3, Expr.v5, Expr.eval, Env.get,
              decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ne_eq,
              not_true_eq_false, StateT.run_set, StateT.run_pure, StateT.run_bind,
              StateT.run_modify, StateT.run_lift, pure_bind, bind_assoc,
              map_eq_bind_pure_comp, Function.comp_def, encWireSt, Prod.map,
              id_eq, encSalts_append_singleton]
            refine bind_congr fun r => ?_
            cases r <;> rfl
          · intro z hz
            simp only [StateT.run_set, StateT.run_pure, StateT.run_bind, StateT.run_modify,
              StateT.run_lift, pure_bind, bind_assoc, ne_eq, not_true_eq_false, ↓reduceIte,
              mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
            obtain ⟨r, -, rfl⟩ := hz
            exact hI.append_of_none hidx st.2.2.1 true
        · refine ⟨by simp [Expr.eval, Env.get, encWireSt, hnj, Prod.map], ?_⟩
          intro z hz
          simp only [StateT.run_set, StateT.run_pure, StateT.run_bind, StateT.run_modify,
            pure_bind, ne_eq, hnj, not_false_eq_true, ↓reduceIte,
            support_pure, Set.mem_singleton_iff] at hz
          subst hz
          exact hI.append_of_none hidx true true
  · have hq : n < q := hroom rfl
    dsimp only [CostedReduction.impl, lWireRedProg]
    rw [handlerImpl_slotOtcca_dec]
    dsimp only [lWireDecC]
    by_cases hcond : (!st.2.2.2 || !(e.2 == a.2.2.salt)) = true
    · refine ⟨?_, ?_⟩
      · simp only [wRedImpl, eval_ite, eval_ret, orE_eval, eqSaltE_eval, saltOfE_eval,
          Expr.v0, Expr.v1, Expr.eval, Env.get, encWireSt, decide_ne_salt, hcond, ↓reduceIte,
          StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, map_pure,
          Prod.map, id_eq]
      · intro z hz
        simp only [wRedImpl, StateT.run_bind, StateT.run_get, pure_bind, decide_ne_salt,
          hcond, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz
        exact hI.preserve_salts st.2.2.1 st.2.2.2
    · simp only [wRedImpl, wSlot, encWireSt, eval_ite, eval_bind_ret, orE_eval, eqSaltE_eval,
        saltOfE_eval, Expr.v0, Expr.v1, Expr.eval, Env.get, decide_ne_salt,
        StateT.run_bind, StateT.run_get, pure_bind, hcond, Bool.false_eq_true, ↓reduceIte]
      rw [wireSlotE_eval C codec ℓ encT idOf kAEAD q st hI hq a.2.2.salt]
      cases hidx : st.1.idxOf? a.2.2.salt with
      | some idx =>
        by_cases hnj : idx = j
        · subst hnj
          refine ⟨?_, ?_⟩
          · simp only [eval_bind, eval_ret, query_wireRed_dec, idsOfE_eval,
              hdrOfE_eval, eqHdrE_eval, fitPlainE_eval,
              Expr.v3, Expr.v5, Expr.eval, Env.get,
              decide_true, ↓reduceIte, StateT.run_pure, StateT.run_bind, StateT.run_lift,
              pure_bind, bind_assoc, map_eq_bind_pure_comp, Function.comp_def,
              encWireSt, Prod.map, id_eq]
            refine bind_congr fun r => ?_
            rcases r with _ | ⟨h, m⟩
            · rfl
            · by_cases hh : h = lHeader encT a.1 a.2.1 a.2.2 <;> simp [hh]
          · intro z hz
            simp only [StateT.run_pure, StateT.run_bind, StateT.run_lift, pure_bind,
              bind_assoc, ↓reduceIte, mem_support_bind_iff, support_pure,
              Set.mem_singleton_iff] at hz
            obtain ⟨r, -, rfl⟩ := hz
            exact hI.preserve_salts st.2.2.1 st.2.2.2
        · refine ⟨by simp [Expr.v4, Expr.eval, Env.get, encWireSt, hnj, Prod.map], ?_⟩
          intro z hz
          simp only [StateT.run_pure, pure_bind, hnj, ↓reduceIte,
            support_pure, Set.mem_singleton_iff] at hz
          subst hz
          exact hI.preserve_salts st.2.2.1 st.2.2.2
      | none =>
        by_cases hnj : st.1.length = j
        · subst hnj
          refine ⟨?_, ?_⟩
          · simp only [eval_bind, eval_ret, query_wireRed_dec, idsOfE_eval,
              hdrOfE_eval, eqHdrE_eval, fitPlainE_eval,
              Expr.v3, Expr.v5, Expr.eval, Env.get,
              decide_true, ↓reduceIte, StateT.run_set, StateT.run_pure, StateT.run_bind,
              StateT.run_lift, pure_bind, bind_assoc, map_eq_bind_pure_comp, Function.comp_def,
              encWireSt, Prod.map, id_eq, encSalts_append_singleton]
            refine bind_congr fun r => ?_
            rcases r with _ | ⟨h, m⟩
            · rfl
            · by_cases hh : h = lHeader encT a.1 a.2.1 a.2.2 <;> simp [hh]
          · intro z hz
            simp only [StateT.run_set, StateT.run_pure, StateT.run_bind, StateT.run_lift,
              pure_bind, bind_assoc, ↓reduceIte, mem_support_bind_iff, support_pure,
              Set.mem_singleton_iff] at hz
            obtain ⟨r, -, rfl⟩ := hz
            exact hI.append_of_none hidx st.2.2.1 st.2.2.2
        · refine ⟨by simp [Expr.v4, Expr.eval, Env.get, encWireSt, hnj, Prod.map], ?_⟩
          intro z hz
          simp only [StateT.run_set, StateT.run_pure, StateT.run_bind, pure_bind,
            hnj, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hz
          subst hz
          exact hI.append_of_none hidx st.2.2.1 st.2.2.2

omit [DecidableEq Pt] in
theorem isQueryBoundP_isRight_of_isGameQuery {κ : Type} {G : OracleSpec κ} {α : Type}
    {oa : OracleComp (unifSpec + G) α} {q : ℕ}
    (h : oa.IsQueryBoundP (isGameQuery (G := G)) q) :
    oa.IsQueryBoundP (fun t => t.isRight = true) q :=
  Computational.Proofs.GameHop.StateSim.isQueryBoundP_congr_pred
    (fun t => by cases t <;> simp [isGameQuery]) h

/-- On any `q`-query OT-CCA adversary `B`, `lWireRedProg j q` evaluates to `lWireRed`. -/
theorem lWireRedProg_eval (j q : ℕ)
    (B : AEADScheme.OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32)
    (hB : B.IsQueryBoundP
      (isGameQuery (G := AEADScheme.otccaSpec (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32)) q) :
    (lWireRedProg C codec ℓ encT idOf kAEAD j q).eval (fun _ => B) () =
      lWireRed C codec ℓ encT idOf j B := by
  have hsim :=
    simulateQ_run_enc_of_bound
      ((lWireRedProg C codec ℓ encT idOf kAEAD j q).impl)
      (wRedImpl C codec ℓ encT idOf j)
      (encWireSt ℓ) (fun t => t.isRight = true) q WireInv
      (lWireRedProg_step_eval C codec ℓ encT idOf kAEAD j q)
      B q (isQueryBoundP_isRight_of_isGameQuery hB) ([], [], false, false) 0
      WireInv.init (by omega)
  dsimp only [CostedReduction.eval, lWireRed]
  change (do
      let q_1 ←
        (simulateQ (lWireRedProg C codec ℓ encT idOf kAEAD j q).impl B).run
          (encWireSt ℓ ([], [], false, false))
      (lWireRedProg C codec ℓ encT idOf kAEAD j q).finish.eval
        (.cons q_1.2 (.cons q_1.1 .nil))) = _
  rw [hsim, bind_map_left]
  refine bind_congr fun ⟨b', st⟩ => ?_
  simp only [lWireRedProg, lWireFinishC, encWireSt, Prod.map, id_eq, eval_ite, eval_ret, orE_eval,
    Expr.v0, Expr.v1, Expr.eval, Env.get, sample_wireRed_bool]
  by_cases hj : j = 0
  · subst hj; rfl
  · simp [hj]

/-! ## `slotSaltRedProg` and `slotWireRedProg` -/

@[simp] def encOSt (s : FSAEAD.Thm5.IndexedOtccaState (BitVec 256) (Header Pt × LibsignalMsgPublicPart) LibsignalCiphertextWithSalt32) :
    (ostTy (Pt := Pt) ℓ).denote :=
  (s.key, (s.b, s.chal))

@[simp] def encSaltSlotSt (st : SaltSlotSt Pt) : (saltSlotStTy (Pt := Pt) ℓ).denote :=
  (st.chal, st.table)

def encTbl {α β : Type} (enc : α → β) (f : ℕ → α) : ℕ → β :=
  fun i => enc (f i)

omit [DecidableEq Pt] in
@[simp] theorem encTbl_apply {α β : Type} (enc : α → β) (f : ℕ → α) (i : ℕ) :
    encTbl enc f i = enc (f i) := rfl

omit [DecidableEq Pt] in
theorem encTbl_update {α β : Type} (enc : α → β) (f : ℕ → α) (i : ℕ) (v : α) :
    (fun j => if j = i then enc v else encTbl enc f j) = encTbl enc (Function.update f i v) := by
  funext j
  by_cases h : j = i <;> simp [Function.update, encTbl, h]

def populateOStTbl : ℕ → (ℕ → (ostTy (Pt := Pt) ℓ).denote) → List (BitVec 256) →
    ℕ → (ostTy (Pt := Pt) ℓ).denote
  | _, tbl, [] => tbl
  | idx, tbl, K :: ks =>
    populateOStTbl (idx + 1) (fun j => if j = idx then (K, (false, none)) else tbl j) ks

omit [DecidableEq Pt] in
theorem populateOStTbl_apply :
    ∀ (ks : List (BitVec 256)) (idx : ℕ) (tbl : ℕ → (ostTy (Pt := Pt) ℓ).denote),
      (∀ j, (tbl j).2 = (false, none)) →
      ∀ j, populateOStTbl ℓ idx tbl ks j =
        (if j < idx then (tbl j).1 else ks[j - idx]?.getD (tbl j).1, (false, none))
  | [], idx, tbl, htbl, j => by
    simp only [populateOStTbl, List.getElem?_nil, Option.getD_none, ite_self]
    exact Prod.ext rfl (htbl j)
  | K :: ks, idx, tbl, htbl, j => by
    let tbl' : ℕ → (ostTy (Pt := Pt) ℓ).denote :=
      fun i => if i = idx then (K, (false, none)) else tbl i
    have htbl' : ∀ i, (tbl' i).2 = (false, none) := by
      intro i; dsimp only [tbl']; split <;> [rfl; exact htbl i]
    rw [populateOStTbl, populateOStTbl_apply ks (idx + 1) tbl' htbl' j]
    congr 1
    by_cases hlt : j < idx
    · have hlt' : j < idx + 1 := by omega
      have hne : j ≠ idx := by omega
      simp [tbl', hlt, hlt', hne]
    · by_cases heq : j = idx
      · subst heq
        simp [tbl']
      · have hgt : ¬ j < idx + 1 := by omega
        have hsub : j - idx = (j - (idx + 1)) + 1 := by omega
        simp [tbl', hlt, heq, hgt, hsub]

omit [DecidableEq Pt] in
theorem populateOStTbl_initOStM (K₀ : BitVec 256) (ks : List (BitVec 256)) :
    populateOStTbl (Pt := Pt) ℓ 1 (fun _ => (K₀, (false, none))) ks =
      encTbl (encOSt ℓ) (FSAEAD.Thm5.initOStM false K₀ ks) := by
  funext j
  rw [populateOStTbl_apply ℓ ks 1 (fun _ => (K₀, (false, none))) (fun _ => rfl) j]
  simp only [encTbl, encOSt, FSAEAD.Thm5.initOStM]
  congr 1
  by_cases hj : j = 0
  · subst hj; rfl
  · have hlt : ¬ j < 1 := by omega
    simp [hj, hlt]

omit [DecidableEq Pt] in
theorem iterM_populateOStTbl :
    ∀ (n idx : ℕ) (tbl : ℕ → (ostTy (Pt := Pt) ℓ).denote),
      iterM
        (fun a : ℕ × (ℕ → (ostTy (Pt := Pt) ℓ).denote) => do
          let K ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
            OracleComp (FSAEAD.Thm5.IndexedOtccaSpec (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (BitVec 256))
          pure (a.1 + 1, fun j => if j = a.1 then (K, (false, none)) else a.2 j))
        n (idx, tbl) =
      (fun ks => (idx + n, populateOStTbl ℓ idx tbl ks)) <$>
        (liftM (FSAEAD.Thm5.sampleKeys (MK := BitVec 256) n) :
          OracleComp (FSAEAD.Thm5.IndexedOtccaSpec (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (List (BitVec 256)))
  | 0, idx, tbl => by
    simp [iterM, FSAEAD.Thm5.sampleKeys, populateOStTbl]
  | n + 1, idx, tbl => by
    simp only [iterM, FSAEAD.Thm5.sampleKeys, monadLift_bind, monadLift_pure,
      map_bind, map_pure, bind_assoc, pure_bind]
    refine bind_congr fun K => ?_
    rw [iterM_populateOStTbl n (idx + 1)
      (fun j => if j = idx then (K, (false, none)) else tbl j)]
    simp only [map_eq_bind_pure_comp, Function.comp_def, populateOStTbl]
    refine bind_congr fun ks => ?_
    rw [show idx + 1 + n = idx + (n + 1) by omega]

omit [DecidableEq Pt] in
theorem find?_salt_eq_lookup :
    ∀ (es : List (Salt32 × DerivedMessageKeys)) (salt : Salt32),
      es.find? (fun p => salt == p.1) = (es.lookup salt).map (salt, ·)
  | [], _ => rfl
  | (s, k) :: es, salt => by
    simp only [List.find?_cons, List.lookup_cons]
    by_cases h : salt = s
    · subst h; simp
    · have hbeq : (salt == s) = false := by simp [h]
      simp [hbeq, find?_salt_eq_lookup es salt]

omit [DecidableEq Pt] in
theorem slotKeyOf_support_length (salt : Salt32) (st : SaltSlotSt Pt) :
    ∀ z ∈ support ((slotKeyOf salt).run st), z.2.table.length ≤ st.table.length + 1 := by
  intro z hz
  simp only [slotKeyOf, StateT.run_mk] at hz
  cases h : st.table.lookup salt with
  | some k =>
    simp only [h, support_pure, Set.mem_singleton_iff] at hz
    subst hz; simp
  | none =>
    simp only [h, support_map, Set.mem_image] at hz
    obtain ⟨k, -, rfl⟩ := hz
    simp

theorem slotKeyOfC_eval (q : ℕ) (salt : Salt32) (st : SaltSlotSt Pt)
    (hst : st.table.length ≤ q) {Γ : List SWT} (ρ : Env Γ) :
    (slotKeyOfC C codec ℓ encT idOf kAEAD kIdeal q).eval
      (.cons salt (.cons (st.chal, st.table) ρ)) =
    liftM (Prod.map id (encSaltSlotSt ℓ) <$> (slotKeyOf salt).run st) := by
  have htake : st.table.take q = st.table := List.take_of_length_le hst
  have hfind :
      List.find? (α := (Ty.prod (S := SWSig) (.base .salt) (.base .msgKey)).denote)
        (fun x => salt == x.1) st.table = (st.table.lookup salt).map (salt, ·) :=
    find?_salt_eq_lookup st.table salt
  simp only [slotKeyOfC, slotKeyOf, StateT.run_mk, eval_caseOpt, eqSaltE_eval,
    Expr.v0, Expr.v1, Expr.eval, Env.get, htake, hfind]
  cases st.table.lookup salt with
  | some k =>
    simp [Option.map, Expr.v2, Expr.eval, Env.get, encSaltSlotSt, Prod.map]
  | none =>
    simp only [Option.map, eval_bind, eval_ret, sample_slotOtcca_msgKey,
      Expr.v2, Expr.eval, Env.get, encSaltSlotSt,
      map_eq_bind_pure_comp, Function.comp_def, monadLift_bind, monadLift_pure,
      bind_assoc, pure_bind, Prod.map, id_eq]

omit [DecidableEq Pt] in
@[simp] theorem run_monadLift_stateT {m : Type → Type} [Monad m] {σ α : Type}
    (x : m α) (s : σ) :
    (monadLift x : StateT σ m α).run s = (x >>= fun a => pure (a, s)) := rfl

theorem otImplEncC_eval (key : BitVec 256) (b : Bool)
    (chal : Option ((ℕ × (Header Pt × LibsignalMsgPublicPart)) × LibsignalCiphertextWithSalt32))
    (a : ℕ × (Header Pt × LibsignalMsgPublicPart)) (m : Plain ℓ) {Γ : List SWT} (ρ : Env Γ) :
    (otImplEncC C codec ℓ encT idOf kAEAD kIdeal).eval
      (.cons (encOSt ℓ ⟨key, b, chal⟩) (.cons (a, m) ρ)) =
    liftM (Prod.map id (encOSt ℓ) <$>
      (FSAEAD.Thm5.otImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf)
        (.inr (.inl ⟨a, m⟩))).run ⟨key, b, chal⟩) := by
  cases chal with
  | some p =>
    simp [otImplEncC, FSAEAD.Thm5.otImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
      AEADScheme.otccaEncryptAdIdeal, encOSt, Expr.v0, Expr.eval, Env.get,
      StateT.run_bind, StateT.run_get, StateT.run_pure, Prod.map]
  | none =>
    cases b <;>
      simp only [otImplEncC, FSAEAD.Thm5.otImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        AEADScheme.otccaEncryptAdIdeal, encOSt, eval_ite, eval_bind, eval_ret,
        sample_slotOtcca_ideal, isSomeE_eval, encRE_eval,
        Expr.v0, Expr.v1, Expr.v2, Expr.eval, Env.get,
        Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        StateT.run_bind, StateT.run_get, StateT.run_set, run_monadLift_stateT, StateT.run_pure,
        pure_bind, bind_assoc, map_eq_bind_pure_comp, Function.comp_def,
        monadLift_bind, monadLift_pure, Prod.map, id_eq]

theorem otImplDecC_eval (key : BitVec 256) (b : Bool)
    (chal : Option ((ℕ × (Header Pt × LibsignalMsgPublicPart)) × LibsignalCiphertextWithSalt32))
    (a : ℕ × (Header Pt × LibsignalMsgPublicPart)) (e : LibsignalCiphertextWithSalt32) {Γ : List SWT} (ρ : Env Γ) :
    (otImplDecC C codec ℓ encT idOf kAEAD kIdeal).eval
      (.cons (encOSt ℓ ⟨key, b, chal⟩) (.cons (a, e) ρ)) =
    liftM (Prod.map id (encOSt ℓ) <$>
      (FSAEAD.Thm5.otImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf)
        (.inr (.inr ⟨a, e⟩))).run ⟨key, b, chal⟩) := by
  cases chal with
  | none =>
    cases b <;>
      simp [otImplDecC, FSAEAD.Thm5.otImpl, QueryImpl.add_apply_inr,
        AEADScheme.otccaDecrypt, encOSt, eqChalSomeE,
        Expr.v0, Expr.v1, Expr.eval, Env.get,
        StateT.run_bind, StateT.run_get, StateT.run_pure, Prod.map]
  | some p =>
    rcases p with ⟨a₀, e₀⟩
    by_cases ha : a₀ = a <;> by_cases he : e₀ = e <;> cases b <;>
      simp [otImplDecC, FSAEAD.Thm5.otImpl, QueryImpl.add_apply_inr,
        AEADScheme.otccaDecrypt, encOSt, eqChalSomeE, eqADE_eval, eqCE_eval,
        Expr.v0, Expr.v1, Expr.v2, Expr.eval, Env.get, ha, he,
        StateT.run_bind, StateT.run_get, StateT.run_pure, Prod.map]

theorem slotSaltEncC_eval (b : Bool) (q : ℕ) (st : SaltSlotSt Pt) (hst : st.table.length ≤ q)
    (a : ℕ × (Header Pt × LibsignalMsgPublicPart)) (m : Plain ℓ) {Γ : List SWT} (ρ : Env Γ) :
    (slotSaltEncC C codec ℓ encT idOf kAEAD kIdeal b q).eval
      (.cons (encSaltSlotSt ℓ st) (.cons (a, m) ρ)) =
    liftM (Prod.map id (encSaltSlotSt ℓ) <$>
      (slotSaltImpl C codec ℓ encT idOf b (.inr (.inl ⟨a, m⟩))).run st) := by
  cases hchal : st.chal with
  | some p =>
    simp [slotSaltEncC, slotSaltImpl, encSaltSlotSt, isSomeE_eval, Expr.v0, Expr.eval, Env.get,
      hchal, StateT.run_bind, StateT.run_get, StateT.run_pure, Prod.map]
  | none =>
    dsimp only [slotSaltEncC, slotSaltImpl, encSaltSlotSt]
    rw [eval_ite]
    simp only [isSomeE_eval, Expr.v0, Expr.v1, Expr.eval, Env.get, hchal, Option.isSome_none,
      Bool.false_eq_true, ↓reduceIte, eval_bind, eval_ret, saltOfE_eval,
      StateT.run_bind, StateT.run_get, pure_bind]
    rw [← hchal, slotKeyOfC_eval C codec ℓ encT idOf kAEAD kIdeal q a.2.2.salt st hst]
    simp only [map_eq_bind_pure_comp, Function.comp_def,
      monadLift_bind, monadLift_pure, bind_assoc, pure_bind]
    refine bind_congr fun p => ?_
    cases b with
    | false =>
      simp only [eval_ite, eval_ret, encKE_eval,
        Expr.v3, Expr.eval, Env.get, encSaltSlotSt, Prod.map, id_eq,
        Bool.false_eq_true, ↓reduceIte,
        StateT.run_bind, StateT.run_modify, StateT.run_pure,
        pure_bind, monadLift_pure]
    | true =>
      simp only [eval_ite, eval_bind, eval_ret, sample_slotOtcca_ideal,
        Expr.v3, Expr.v4, Expr.eval, Env.get, encSaltSlotSt, Prod.map, id_eq,
        ↓reduceIte,
        StateT.run_bind, StateT.run_modify, StateT.run_lift, StateT.run_pure,
        pure_bind, bind_assoc, monadLift_bind, monadLift_pure]

theorem slotSaltDecC_false_eval (b : Bool) (q : ℕ) (st : SaltSlotSt Pt)
    (hst : st.table.length ≤ q) (a : ℕ × (Header Pt × LibsignalMsgPublicPart)) (e : LibsignalCiphertextWithSalt32)
    {Γ : List SWT} (ρ : Env Γ) :
    (slotSaltDecC C codec ℓ encT idOf kAEAD kIdeal false b q).eval
      (.cons (encSaltSlotSt ℓ st) (.cons (a, e) ρ)) =
    liftM (Prod.map id (encSaltSlotSt ℓ) <$>
      (slotSaltImpl C codec ℓ encT idOf b (.inr (.inr ⟨a, e⟩))).run st) := by
  dsimp only [slotSaltDecC, slotSaltImpl, encSaltSlotSt]
  rw [eval_ite]
  by_cases hs : e.2 = a.2.2.salt
  · simp only [eqSaltE_eval, saltOfE_eval, Expr.v1, Expr.eval, Env.get, hs,
      beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      ne_eq, not_true_eq_false, StateT.run_bind, StateT.run_get, pure_bind]
    rw [eval_ite]
    by_cases hcond : (b || st.chal == some (a, e)) = true
    · simp only [orE_eval, eqChalSomeE_v1_eval, Expr.v0, Expr.eval, Env.get,
        hcond, ↓reduceIte, eval_ret, StateT.run_pure, map_pure, monadLift_pure,
        encSaltSlotSt, Prod.map, id_eq]
    · simp only [orE_eval, eqChalSomeE_v1_eval, Expr.v0, Expr.eval, Env.get,
        hcond, Bool.false_eq_true, ↓reduceIte, eval_bind, eval_ret, pure_bind,
        saltOfE_eval, decKE_eval, Expr.v3]
      rw [slotKeyOfC_eval C codec ℓ encT idOf kAEAD kIdeal q a.2.2.salt st hst]
      simp only [StateT.run_bind, StateT.run_pure, map_eq_bind_pure_comp, Function.comp_def,
        monadLift_bind, monadLift_pure, bind_assoc, pure_bind, encSaltSlotSt, Prod.map, id_eq]
  · simp [eqSaltE_eval, saltOfE_eval, Expr.v0, Expr.v1, Expr.eval, Env.get, hs,
      StateT.run_pure, Prod.map]

theorem slotSaltDecC_true_eval (b : Bool) (q : ℕ) (st : SaltSlotSt Pt)
    (hst : st.table.length ≤ q) (a : ℕ × (Header Pt × LibsignalMsgPublicPart)) (e : LibsignalCiphertextWithSalt32)
    {Γ : List SWT} (ρ : Env Γ) :
    (slotSaltDecC C codec ℓ encT idOf kAEAD kIdeal true b q).eval
      (.cons (encSaltSlotSt ℓ st) (.cons (a, e) ρ)) =
    liftM (Prod.map id (encSaltSlotSt ℓ) <$>
      (slotSaltImplNF C codec ℓ encT idOf b (.inr (.inr ⟨a, e⟩))).run st) := by
  dsimp only [slotSaltDecC, slotSaltImplNF, encSaltSlotSt]
  rw [eval_ite]
  by_cases hs : e.2 = a.2.2.salt
  · simp only [eqSaltE_eval, saltOfE_eval, Expr.v1, Expr.eval, Env.get, hs,
      beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      ne_eq, not_true_eq_false, StateT.run_bind, StateT.run_get, pure_bind]
    rw [eval_ite]
    by_cases hcond :
        ((b || !isSlotChalSalt st.chal a.2.2.salt) || st.chal == some (a, e)) = true
    · simp only [orE_eval, eqChalSomeE_v1_eval, isSlotChalSaltE_v1_eval,
        Expr.v0, Expr.eval, Env.get, hcond, ↓reduceIte, eval_ret,
        StateT.run_pure, map_pure, monadLift_pure, encSaltSlotSt, Prod.map, id_eq]
    · simp only [orE_eval, eqChalSomeE_v1_eval, isSlotChalSaltE_v1_eval,
        Expr.v0, Expr.eval, Env.get, hcond, Bool.false_eq_true, ↓reduceIte,
        eval_bind, eval_ret, pure_bind, saltOfE_eval, decKE_eval, Expr.v3]
      rw [slotKeyOfC_eval C codec ℓ encT idOf kAEAD kIdeal q a.2.2.salt st hst]
      simp only [StateT.run_bind, StateT.run_pure, map_eq_bind_pure_comp, Function.comp_def,
        monadLift_bind, monadLift_pure, bind_assoc, pure_bind, encSaltSlotSt, Prod.map, id_eq]
  · simp [eqSaltE_eval, saltOfE_eval, Expr.v0, Expr.v1, Expr.eval, Env.get, hs,
      StateT.run_pure, Prod.map]

theorem slotSaltImpl_support_length (b : Bool)
    (t : (AEADScheme.otccaSpec (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32).Domain)
    (st : SaltSlotSt Pt) :
    ∀ z ∈ support ((slotSaltImpl C codec ℓ encT idOf b (.inr t)).run st),
      z.2.table.length ≤ st.table.length + 1 := by
  intro z hz
  rcases t with ⟨a, m⟩ | ⟨a, e⟩
  · simp only [slotSaltImpl, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; simp
    · simp only [StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨⟨mk, st₁⟩, hmk, hz⟩ := hz
      have hlen := slotKeyOf_support_length a.2.2.salt st (mk, st₁) hmk
      cases b with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_modify,
          StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hlen
      | true =>
        simp only [↓reduceIte, StateT.run_bind, StateT.run_lift, StateT.run_modify,
          StateT.run_pure, bind_assoc, pure_bind, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hz
        obtain ⟨c, -, rfl⟩ := hz; exact hlen
  · simp only [slotSaltImpl] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; simp
    · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
      split at hz
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; simp
      · simp only [StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hz
        obtain ⟨⟨mk, st₁⟩, hmk, rfl⟩ := hz
        exact slotKeyOf_support_length a.2.2.salt st (mk, st₁) hmk

theorem slotSaltImplNF_support_length (b : Bool)
    (t : (AEADScheme.otccaSpec (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32).Domain)
    (st : SaltSlotSt Pt) :
    ∀ z ∈ support ((slotSaltImplNF C codec ℓ encT idOf b (.inr t)).run st),
      z.2.table.length ≤ st.table.length + 1 := by
  intro z hz
  rcases t with ⟨a, m⟩ | ⟨a, e⟩
  · simp only [slotSaltImplNF, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; simp
    · simp only [StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨⟨mk, st₁⟩, hmk, hz⟩ := hz
      have hlen := slotKeyOf_support_length a.2.2.salt st (mk, st₁) hmk
      cases b with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_modify,
          StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hlen
      | true =>
        simp only [↓reduceIte, StateT.run_bind, StateT.run_lift, StateT.run_modify,
          StateT.run_pure, bind_assoc, pure_bind, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hz
        obtain ⟨c, -, rfl⟩ := hz; exact hlen
  · simp only [slotSaltImplNF] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; simp
    · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
      split at hz
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; simp
      · simp only [StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hz
        obtain ⟨⟨mk, st₁⟩, hmk, rfl⟩ := hz
        exact slotKeyOf_support_length a.2.2.salt st (mk, st₁) hmk

theorem slotRedHandleC_step_eval {SL SR : Type} {slTy srTy : SWT} (k : ℕ)
    (encL : SL → slTy.denote) (encR : SR → srTy.denote)
    (implL : QueryImpl (FSAEAD.Thm5.IndexedOtccaSpec (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)
      (StateT SL ProbComp))
    (implR : QueryImpl (FSAEAD.Thm5.IndexedOtccaSpec (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32)
      (StateT SR ProbComp))
    (encLC : ∀ {Γ},
      Comp SWOps SlotIface (slTy :: .prod (slotAdTy Pt ℓ) (.base .plain) :: Γ)
        (.prod (.opt (lctTy Pt ℓ)) slTy))
    (decLC : ∀ {Γ},
      Comp SWOps SlotIface (slTy :: .prod (slotAdTy Pt ℓ) (lctTy Pt ℓ) :: Γ)
        (.prod (.opt (.base .plain)) slTy))
    (encRC : ∀ {Γ},
      Comp SWOps SlotIface (srTy :: .prod (slotAdTy Pt ℓ) (.base .plain) :: Γ)
        (.prod (.opt (lctTy Pt ℓ)) srTy))
    (decRC : ∀ {Γ},
      Comp SWOps SlotIface (srTy :: .prod (slotAdTy Pt ℓ) (lctTy Pt ℓ) :: Γ)
        (.prod (.opt (.base .plain)) srTy))
    (s : (ℕ → SL) × (ℕ → SR))
    (t : (FSAEAD.Thm5.IndexedOtccaSpec (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32).Domain)
    (hEncL : t.isRight = true → ∀ i a m {Γ} (ρ : Env Γ),
      encLC.eval (.cons (encL (s.1 i)) (.cons (a, m) ρ)) =
        liftM (Prod.map id encL <$> (implL (.inr (.inl ⟨a, m⟩))).run (s.1 i)))
    (hDecL : t.isRight = true → ∀ i a e {Γ} (ρ : Env Γ),
      decLC.eval (.cons (encL (s.1 i)) (.cons (a, e) ρ)) =
        liftM (Prod.map id encL <$> (implL (.inr (.inr ⟨a, e⟩))).run (s.1 i)))
    (hEncR : t.isRight = true → ∀ i a m {Γ} (ρ : Env Γ),
      encRC.eval (.cons (encR (s.2 i)) (.cons (a, m) ρ)) =
        liftM (Prod.map id encR <$> (implR (.inr (.inl ⟨a, m⟩))).run (s.2 i)))
    (hDecR : t.isRight = true → ∀ i a e {Γ} (ρ : Env Γ),
      decRC.eval (.cons (encR (s.2 i)) (.cons (a, e) ρ)) =
        liftM (Prod.map id encR <$> (implR (.inr (.inr ⟨a, e⟩))).run (s.2 i))) :
    ((handlerImpl (C := SlotCodec)
      (slotRedHandleC C codec ℓ encT idOf kAEAD kIdeal k encLC decLC encRC decRC) t).run
      (encTbl encL s.1, encTbl encR s.2)) =
    Prod.map id (Prod.map (encTbl encL) (encTbl encR)) <$>
      (FSAEAD.Thm5.slotRedImpl implL implR k t).run s := by
  rcases t with n | (⟨h, m⟩ | ⟨h, e⟩)
  · exact run_lift_map_enc _ (Prod.map (encTbl encL) (encTbl encR)) s
  · dsimp only [slotRedHandleC]
    rw [handlerImpl_slotOtcca_enc]
    dsimp only [slotRedEncC]
    by_cases hk : h.1 = k + 1
    · simp only [FSAEAD.Thm5.slotRedImpl, eval_ite, eval_bind, eval_ret, query_slotOtcca_enc_v0,
        Expr.v0, Expr.v2, Expr.eval, Env.get, hk, decide_true, ↓reduceIte,
        StateT.run_lift, map_eq_bind_pure_comp, Function.comp_def,
        bind_assoc, pure_bind, Prod.map, id_eq]
      rfl
    · by_cases hr : 1 ≤ h.1 ∧ h.1 ≤ k
      · simp only [FSAEAD.Thm5.slotRedImpl, eval_ite, eval_bind, eval_ret, pure_bind,
          leE_eval, Expr.v0, Expr.v1, Expr.eval, Env.get, encTbl_apply,
          hk, decide_false, Bool.false_eq_true, ↓reduceIte, hr, decide_true, Bool.and_self,
          and_self, StateT.run_mk]
        rw [hEncR rfl h.1 h m]
        simp only [Expr.v2, Expr.v3, Expr.eval, Env.get,
          map_eq_bind_pure_comp, Function.comp_def, monadLift_bind, monadLift_pure,
          bind_assoc, pure_bind, Prod.map, id_eq, encTbl_update]
      · have hcond : (decide (1 ≤ h.1) && decide (h.1 ≤ k)) = false := by
          rw [Bool.and_eq_false_iff]
          by_cases h1 : 1 ≤ h.1
          · right; simp [show ¬ h.1 ≤ k by omega]
          · left; simp [h1]
        simp only [FSAEAD.Thm5.slotRedImpl, eval_ite, eval_bind, eval_ret, pure_bind,
          leE_eval, Expr.v0, Expr.v1, Expr.eval, Env.get, encTbl_apply,
          hk, decide_false, Bool.false_eq_true, ↓reduceIte, hr, hcond, StateT.run_mk]
        rw [hEncL rfl h.1 h m]
        simp only [Expr.v2, Expr.v3, Expr.eval, Env.get,
          map_eq_bind_pure_comp, Function.comp_def, monadLift_bind, monadLift_pure,
          bind_assoc, pure_bind, Prod.map, id_eq, encTbl_update]
  · dsimp only [slotRedHandleC]
    rw [handlerImpl_slotOtcca_dec]
    dsimp only [slotRedDecC]
    by_cases hk : h.1 = k + 1
    · simp only [FSAEAD.Thm5.slotRedImpl, eval_ite, eval_bind, eval_ret, query_slotOtcca_dec_v0,
        Expr.v0, Expr.v2, Expr.eval, Env.get, hk, decide_true, ↓reduceIte,
        StateT.run_lift, map_eq_bind_pure_comp, Function.comp_def,
        bind_assoc, pure_bind, Prod.map, id_eq]
      rfl
    · by_cases hr : 1 ≤ h.1 ∧ h.1 ≤ k
      · simp only [FSAEAD.Thm5.slotRedImpl, eval_ite, eval_bind, eval_ret, pure_bind,
          leE_eval, Expr.v0, Expr.v1, Expr.eval, Env.get, encTbl_apply,
          hk, decide_false, Bool.false_eq_true, ↓reduceIte, hr, decide_true, Bool.and_self,
          and_self, StateT.run_mk]
        rw [hDecR rfl h.1 h e]
        simp only [Expr.v2, Expr.v3, Expr.eval, Env.get,
          map_eq_bind_pure_comp, Function.comp_def, monadLift_bind, monadLift_pure,
          bind_assoc, pure_bind, Prod.map, id_eq, encTbl_update]
      · have hcond : (decide (1 ≤ h.1) && decide (h.1 ≤ k)) = false := by
          rw [Bool.and_eq_false_iff]
          by_cases h1 : 1 ≤ h.1
          · right; simp [show ¬ h.1 ≤ k by omega]
          · left; simp [h1]
        simp only [FSAEAD.Thm5.slotRedImpl, eval_ite, eval_bind, eval_ret, pure_bind,
          leE_eval, Expr.v0, Expr.v1, Expr.eval, Env.get, encTbl_apply,
          hk, decide_false, Bool.false_eq_true, ↓reduceIte, hr, hcond, StateT.run_mk]
        rw [hDecL rfl h.1 h e]
        simp only [Expr.v2, Expr.v3, Expr.eval, Env.get,
          map_eq_bind_pure_comp, Function.comp_def, monadLift_bind, monadLift_pure,
          bind_assoc, pure_bind, Prod.map, id_eq, encTbl_update]

omit [DecidableEq Pt] in
theorem mem_support_liftM_probComp {κ : Type} {G : OracleSpec.{0, 0} κ} {α : Type}
    (p : ProbComp α) (z : α) :
    z ∈ support (liftM p : OracleComp (unifSpec + G) α) ↔ z ∈ support p := by
  induction p using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx ih =>
    simp only [monadLift_bind, mem_support_bind_iff]
    constructor
    · rintro ⟨u, -, hz⟩
      exact ⟨u, mem_support_query t u, (ih u).mp hz⟩
    · rintro ⟨u, -, hz⟩
      refine ⟨u, ?_, (ih u).mpr hz⟩
      exact mem_support_query (spec := unifSpec + G) (Sum.inl t) u

/-- Query-budget invariant for `slotSaltRed`: every right-hand slot table has length `≤ n`. -/
def SlotSaltInv (n : ℕ)
    (s : (ℕ → FSAEAD.Thm5.IndexedOtccaState (BitVec 256) (Header Pt × LibsignalMsgPublicPart) LibsignalCiphertextWithSalt32) × (ℕ → SaltSlotSt Pt)) :
    Prop :=
  ∀ i, (s.2 i).table.length ≤ n

theorem slotSaltRed_preserve_inv (k : ℕ)
    (t : (FSAEAD.Thm5.IndexedOtccaSpec (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32).Domain)
    (s : (ℕ → FSAEAD.Thm5.IndexedOtccaState (BitVec 256) (Header Pt × LibsignalMsgPublicPart) LibsignalCiphertextWithSalt32) × (ℕ → SaltSlotSt Pt))
    (n : ℕ) (hI : SlotSaltInv n s) :
    ∀ z ∈ support
      ((FSAEAD.Thm5.slotRedImpl
        (FSAEAD.Thm5.otImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf))
        (slotSaltImpl C codec ℓ encT idOf false) k t).run s),
      SlotSaltInv (if t.isRight = true then n + 1 else n) z.2 := by
  intro z hz
  rcases t with m | (⟨h, msg⟩ | ⟨h, e⟩)
  · simp only [FSAEAD.Thm5.slotRedImpl, StateT.run_lift, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact hI
  · simp only [FSAEAD.Thm5.slotRedImpl] at hz
    split_ifs at hz with hk hr
    · simp only [StateT.run_lift, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hz
      obtain ⟨u, -, rfl⟩ := hz
      intro i; exact Nat.le_succ_of_le (hI i)
    · simp only [StateT.run_mk, mem_support_liftM_probComp, support_map, Set.mem_image] at hz
      obtain ⟨⟨ans, st'⟩, hst, rfl⟩ := hz
      intro i
      by_cases hi : i = h.1
      · subst hi
        simp only [Function.update_self]
        exact (slotSaltImpl_support_length C codec ℓ encT idOf false (.inl ⟨h, msg⟩)
          (s.2 h.1) (ans, st') hst).trans (Nat.add_le_add_right (hI h.1) 1)
      · simp only [Function.update_of_ne hi]
        exact Nat.le_succ_of_le (hI i)
    · simp only [StateT.run_mk, mem_support_liftM_probComp, support_map, Set.mem_image] at hz
      obtain ⟨⟨ans, st'⟩, -, rfl⟩ := hz
      intro i; exact Nat.le_succ_of_le (hI i)
  · simp only [FSAEAD.Thm5.slotRedImpl] at hz
    split_ifs at hz with hk hr
    · simp only [StateT.run_lift, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hz
      obtain ⟨u, -, rfl⟩ := hz
      intro i; exact Nat.le_succ_of_le (hI i)
    · simp only [StateT.run_mk, mem_support_liftM_probComp, support_map, Set.mem_image] at hz
      obtain ⟨⟨ans, st'⟩, hst, rfl⟩ := hz
      intro i
      by_cases hi : i = h.1
      · subst hi
        simp only [Function.update_self]
        exact (slotSaltImpl_support_length C codec ℓ encT idOf false (.inr ⟨h, e⟩)
          (s.2 h.1) (ans, st') hst).trans (Nat.add_le_add_right (hI h.1) 1)
      · simp only [Function.update_of_ne hi]
        exact Nat.le_succ_of_le (hI i)
    · simp only [StateT.run_mk, mem_support_liftM_probComp, support_map, Set.mem_image] at hz
      obtain ⟨⟨ans, st'⟩, -, rfl⟩ := hz
      intro i; exact Nat.le_succ_of_le (hI i)

/-- On any `q`-query OT-CCA adversary `B`, `slotSaltRedProg N k q` evaluates to `slotSaltRed`. -/
theorem slotSaltRedProg_eval (N k q : ℕ)
    (B : AEADScheme.OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32)
    (hB : B.IsQueryBoundP
      (isGameQuery (G := AEADScheme.otccaSpec (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32)) q) :
    (slotSaltRedProg C codec ℓ encT idOf kAEAD kIdeal N k q).eval (fun _ => B) () =
      slotSaltRed C codec ℓ encT idOf N k B := by
  have hsim := fun (K₀ : BitVec 256) (ks : List (BitVec 256)) =>
    simulateQ_run_enc_of_bound
      ((slotSaltRedProg C codec ℓ encT idOf kAEAD kIdeal N k q).impl)
      (FSAEAD.Thm5.slotRedImpl
        (FSAEAD.Thm5.otImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf))
        (slotSaltImpl C codec ℓ encT idOf false) k)
      (Prod.map (encTbl (encOSt ℓ)) (encTbl (encSaltSlotSt ℓ)))
      (fun t => t.isRight = true) q SlotSaltInv
      (fun t s n hI hroom =>
        ⟨slotRedHandleC_step_eval C codec ℓ encT idOf kAEAD kIdeal k
          (encOSt ℓ) (encSaltSlotSt ℓ)
          (FSAEAD.Thm5.otImpl (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf))
          (slotSaltImpl C codec ℓ encT idOf false)
          (otImplEncC C codec ℓ encT idOf kAEAD kIdeal)
          (otImplDecC C codec ℓ encT idOf kAEAD kIdeal)
          (slotSaltEncC C codec ℓ encT idOf kAEAD kIdeal false q)
          (slotSaltDecC C codec ℓ encT idOf kAEAD kIdeal false false q) s t
          (fun _ i a m _ ρ => otImplEncC_eval C codec ℓ encT idOf kAEAD kIdeal
            (s.1 i).key (s.1 i).b (s.1 i).chal a m ρ)
          (fun _ i a e _ ρ => otImplDecC_eval C codec ℓ encT idOf kAEAD kIdeal
            (s.1 i).key (s.1 i).b (s.1 i).chal a e ρ)
          (fun ht i a m _ ρ => slotSaltEncC_eval C codec ℓ encT idOf kAEAD kIdeal false q
            (s.2 i) (by have := hI i; have := hroom ht; omega) a m ρ)
          (fun ht i a e _ ρ => slotSaltDecC_false_eval C codec ℓ encT idOf kAEAD kIdeal false q
            (s.2 i) (by have := hI i; have := hroom ht; omega) a e ρ),
         slotSaltRed_preserve_inv C codec ℓ encT idOf k t s n hI⟩)
      B q (isQueryBoundP_isRight_of_isGameQuery hB)
      (FSAEAD.Thm5.initOStM false K₀ ks, fun _ => {}) 0
      (fun _ => le_rfl) (by omega)
  have hinit :
      (slotSaltRedProg C codec ℓ encT idOf kAEAD kIdeal N k q).init.eval (.cons () .nil) =
        (do
          let K₀ ← (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
            OracleComp (FSAEAD.Thm5.IndexedOtccaSpec (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (BitVec 256))
          let ks ← (liftM (FSAEAD.Thm5.sampleKeys (MK := BitVec 256) N) :
            OracleComp (FSAEAD.Thm5.IndexedOtccaSpec (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32) (List (BitVec 256)))
          pure ((),
            Prod.map (encTbl (encOSt ℓ)) (encTbl (encSaltSlotSt ℓ))
              (FSAEAD.Thm5.initOStM false K₀ ks, fun _ => {}))) := by
    simp only [slotSaltRedProg, slotSaltInitC, eval_bind, eval_iter, eval_ret,
      emptySaltSlotStE_eval, Expr.v0, Expr.v1, Expr.eval, Env.get, sample_slotOtcca_seed]
    refine bind_congr fun K₀ => ?_
    have hiter := iterM_populateOStTbl (Pt := Pt) ℓ N 1 (fun _ => (K₀, (false, none)))
    rw [hiter, bind_map_left]
    refine bind_congr fun ks => ?_
    dsimp only [Prod.map]
    rw [populateOStTbl_initOStM (Pt := Pt) ℓ K₀ ks]
    rfl
  dsimp only [CostedReduction.eval, slotSaltRed]
  change (do
      let p ← (slotSaltRedProg C codec ℓ encT idOf kAEAD kIdeal N k q).init.eval (.cons () .nil)
      let q_1 ← (simulateQ (slotSaltRedProg C codec ℓ encT idOf kAEAD kIdeal N k q).impl B).run p.2
      (slotSaltRedProg C codec ℓ encT idOf kAEAD kIdeal N k q).finish.eval
        (.cons q_1.2 (.cons q_1.1 .nil))) = _
  rw [hinit]
  simp only [bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_def]
  refine bind_congr fun K₀ => bind_congr fun ks => ?_
  rw [hsim K₀ ks, bind_map_left]
  rfl

/-- Query-budget invariant for `slotWireRed`: every left-hand and right-hand slot table has length
`≤ n`. -/
def SlotWireInv (n : ℕ) (s : (ℕ → SaltSlotSt Pt) × (ℕ → SaltSlotSt Pt)) : Prop :=
  (∀ i, (s.1 i).table.length ≤ n) ∧ (∀ i, (s.2 i).table.length ≤ n)

theorem slotWireRed_preserve_inv (k : ℕ)
    (t : (FSAEAD.Thm5.IndexedOtccaSpec (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32).Domain)
    (s : (ℕ → SaltSlotSt Pt) × (ℕ → SaltSlotSt Pt))
    (n : ℕ) (hI : SlotWireInv n s) :
    ∀ z ∈ support
      ((FSAEAD.Thm5.slotRedImpl
        (slotSaltImplNF C codec ℓ encT idOf false)
        (slotSaltImpl C codec ℓ encT idOf true) k t).run s),
      SlotWireInv (if t.isRight = true then n + 1 else n) z.2 := by
  intro z hz
  rcases t with m | (⟨h, msg⟩ | ⟨h, e⟩)
  · simp only [FSAEAD.Thm5.slotRedImpl, StateT.run_lift, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact hI
  · simp only [FSAEAD.Thm5.slotRedImpl] at hz
    split_ifs at hz with hk hr
    · simp only [StateT.run_lift, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hz
      obtain ⟨u, -, rfl⟩ := hz
      exact ⟨fun i => Nat.le_succ_of_le (hI.1 i), fun i => Nat.le_succ_of_le (hI.2 i)⟩
    · simp only [StateT.run_mk, mem_support_liftM_probComp, support_map, Set.mem_image] at hz
      obtain ⟨⟨ans, st'⟩, hst, rfl⟩ := hz
      refine ⟨fun i => Nat.le_succ_of_le (hI.1 i), fun i => ?_⟩
      by_cases hi : i = h.1
      · subst hi
        simp only [Function.update_self]
        exact (slotSaltImpl_support_length C codec ℓ encT idOf true (.inl ⟨h, msg⟩)
          (s.2 h.1) (ans, st') hst).trans (Nat.add_le_add_right (hI.2 h.1) 1)
      · simp only [Function.update_of_ne hi]
        exact Nat.le_succ_of_le (hI.2 i)
    · simp only [StateT.run_mk, mem_support_liftM_probComp, support_map, Set.mem_image] at hz
      obtain ⟨⟨ans, st'⟩, hst, rfl⟩ := hz
      refine ⟨fun i => ?_, fun i => Nat.le_succ_of_le (hI.2 i)⟩
      by_cases hi : i = h.1
      · subst hi
        simp only [Function.update_self]
        exact (slotSaltImplNF_support_length C codec ℓ encT idOf false (.inl ⟨h, msg⟩)
          (s.1 h.1) (ans, st') hst).trans (Nat.add_le_add_right (hI.1 h.1) 1)
      · simp only [Function.update_of_ne hi]
        exact Nat.le_succ_of_le (hI.1 i)
  · simp only [FSAEAD.Thm5.slotRedImpl] at hz
    split_ifs at hz with hk hr
    · simp only [StateT.run_lift, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hz
      obtain ⟨u, -, rfl⟩ := hz
      exact ⟨fun i => Nat.le_succ_of_le (hI.1 i), fun i => Nat.le_succ_of_le (hI.2 i)⟩
    · simp only [StateT.run_mk, mem_support_liftM_probComp, support_map, Set.mem_image] at hz
      obtain ⟨⟨ans, st'⟩, hst, rfl⟩ := hz
      refine ⟨fun i => Nat.le_succ_of_le (hI.1 i), fun i => ?_⟩
      by_cases hi : i = h.1
      · subst hi
        simp only [Function.update_self]
        exact (slotSaltImpl_support_length C codec ℓ encT idOf true (.inr ⟨h, e⟩)
          (s.2 h.1) (ans, st') hst).trans (Nat.add_le_add_right (hI.2 h.1) 1)
      · simp only [Function.update_of_ne hi]
        exact Nat.le_succ_of_le (hI.2 i)
    · simp only [StateT.run_mk, mem_support_liftM_probComp, support_map, Set.mem_image] at hz
      obtain ⟨⟨ans, st'⟩, hst, rfl⟩ := hz
      refine ⟨fun i => ?_, fun i => Nat.le_succ_of_le (hI.2 i)⟩
      by_cases hi : i = h.1
      · subst hi
        simp only [Function.update_self]
        exact (slotSaltImplNF_support_length C codec ℓ encT idOf false (.inr ⟨h, e⟩)
          (s.1 h.1) (ans, st') hst).trans (Nat.add_le_add_right (hI.1 h.1) 1)
      · simp only [Function.update_of_ne hi]
        exact Nat.le_succ_of_le (hI.1 i)

/-- On any `q`-query OT-CCA adversary `B`, `slotWireRedProg k q` evaluates to `slotWireRed`. -/
theorem slotWireRedProg_eval (k q : ℕ)
    (B : AEADScheme.OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32)
    (hB : B.IsQueryBoundP
      (isGameQuery (G := AEADScheme.otccaSpec (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32)) q) :
    (slotWireRedProg C codec ℓ encT idOf kAEAD kIdeal k q).eval (fun _ => B) () =
      slotWireRed C codec ℓ encT idOf k B := by
  have hsim :=
    simulateQ_run_enc_of_bound
      ((slotWireRedProg C codec ℓ encT idOf kAEAD kIdeal k q).impl)
      (FSAEAD.Thm5.slotRedImpl
        (slotSaltImplNF C codec ℓ encT idOf false)
        (slotSaltImpl C codec ℓ encT idOf true) k)
      (Prod.map (encTbl (encSaltSlotSt ℓ)) (encTbl (encSaltSlotSt ℓ)))
      (fun t => t.isRight = true) q SlotWireInv
      (fun t s n hI hroom =>
        ⟨slotRedHandleC_step_eval C codec ℓ encT idOf kAEAD kIdeal k
          (encSaltSlotSt ℓ) (encSaltSlotSt ℓ)
          (slotSaltImplNF C codec ℓ encT idOf false)
          (slotSaltImpl C codec ℓ encT idOf true)
          (slotSaltEncC C codec ℓ encT idOf kAEAD kIdeal false q)
          (slotSaltDecC C codec ℓ encT idOf kAEAD kIdeal true false q)
          (slotSaltEncC C codec ℓ encT idOf kAEAD kIdeal true q)
          (slotSaltDecC C codec ℓ encT idOf kAEAD kIdeal false true q) s t
          (fun ht i a m _ ρ => slotSaltEncC_eval C codec ℓ encT idOf kAEAD kIdeal false q
            (s.1 i) (by have := hI.1 i; have := hroom ht; omega) a m ρ)
          (fun ht i a e _ ρ => slotSaltDecC_true_eval C codec ℓ encT idOf kAEAD kIdeal false q
            (s.1 i) (by have := hI.1 i; have := hroom ht; omega) a e ρ)
          (fun ht i a m _ ρ => slotSaltEncC_eval C codec ℓ encT idOf kAEAD kIdeal true q
            (s.2 i) (by have := hI.2 i; have := hroom ht; omega) a m ρ)
          (fun ht i a e _ ρ => slotSaltDecC_false_eval C codec ℓ encT idOf kAEAD kIdeal true q
            (s.2 i) (by have := hI.2 i; have := hroom ht; omega) a e ρ),
         slotWireRed_preserve_inv C codec ℓ encT idOf k t s n hI⟩)
      B q (isQueryBoundP_isRight_of_isGameQuery hB)
      (fun _ => {}, fun _ => {}) 0
      ⟨fun _ => le_rfl, fun _ => le_rfl⟩ (by omega)
  dsimp only [CostedReduction.eval, slotWireRed]
  change (do
      let q_1 ←
        (simulateQ (slotWireRedProg C codec ℓ encT idOf kAEAD kIdeal k q).impl B).run
          (Prod.map (encTbl (encSaltSlotSt ℓ)) (encTbl (encSaltSlotSt ℓ))
            (fun _ => {}, fun _ => {}))
      (slotWireRedProg C codec ℓ encT idOf kAEAD kIdeal k q).finish.eval
        (.cons q_1.2 (.cons q_1.1 .nil))) = _
  rw [hsim, bind_map_left, map_eq_bind_pure_comp]
  rfl

theorem slotWireRedProg_queries (k q : ℕ)
    (B : AEADScheme.OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32)
    (hB : B.IsQueryBoundP
      (isGameQuery (G := AEADScheme.otccaSpec (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32)) q) :
    ((slotWireRedProg C codec ℓ encT idOf kAEAD kIdeal k q).eval (fun _ => B) ()).IsQueryBoundP
      (isGameQuery (G := AEADScheme.otccaSpec (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32)) q := by
  have h := CostedReduction.queryBound_eval
    (slotWireRedProg C codec ℓ encT idOf kAEAD kIdeal k q)
    (isGameQuery (G := AEADScheme.otccaSpec (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32))
    (fun _ => 1) (fun _ => 0)
    (fun _ _ _ => le_rfl)
    (fun n => by simp [Iface.withSamp, otccaIface, isGameQuery])
    (fun _ => B) q (fun _ => hB) ()
  refine h.mono (le_of_eq ?_)
  simp [CostedReduction.totalQueries, slotWireRedProg, slotRedHandleC, slotRedEncC, slotRedDecC,
    slotSaltEncC, slotSaltDecC, slotKeyOfC, sampleSlotIdealC, sampleSlotMsgKeyC,
    querySlotEncC, querySlotDecC, Comp.queries]

end CryptoGames.Ratchet.LibsignalInst.Costed

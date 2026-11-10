/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.SpkLeakRedModel
public import Computational.Proofs.SpecLemmas.Reductions.E2E.CostedTables
public import Computational.Proofs.ReductionDsl.SM.GameCosted
public import Computational.Proofs.E2E.SpkHop2Red
public import Computational.Proofs.ReductionDsl.Soundness
import Computational.Proofs.ReductionDsl.Bridge
import Computational.Proofs.ReductionDsl.Notation
import Computational.Proofs.ReductionDsl.Size
import Computational.Proofs.ReductionDsl.Tables

/-!
# Costed `spkLeakRed` Reduction

Defines `spkLeakRedProg` as a `ReductionDsl.CostedReduction` program for the PRF reduction
`spkLeakRed` (hops 1 and 3 of the leaked signed-pre-key proof), with size-honesty lemmas,
evaluation agreement, and cost bounds.
-/

@[expose] public section

namespace CryptoVerification.E2E.Costed

open ReductionDsl OracleComp OracleSpec CryptoGames CryptoGames.SM CryptoGames.PRF.Costed
  CryptoGames.PRG.Costed CryptoGames.LibsignalSM CryptoGames.Ratchet
  CryptoGames.Ratchet.LibsignalInst CryptoGames.LibsignalSession CryptoGames.CKA
  CryptoGames.MACScheme CryptoGames.HKDF CryptoGames.HMAC CBC
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession
  CryptoVerification.E2E
open Computational.Proofs.GameHop.CompDedup
  (CountLe countLe_nil countLe_cons_cons countLe_cons_right countLe_filter_left
    countLe_dedupPrepend afterCorrDedup corrRDedup)
open scoped Computational.Proofs.ReductionDsl.Notation

local macro_rules
  | `(rdsl_pat| .transmit $p:term)  => `(rdsl_pat| .inl (.inl (.inl (.inl $p))))
  | `(rdsl_pat| .challenge $p:term) => `(rdsl_pat| .inl (.inl (.inl (.inr $p))))
  | `(rdsl_pat| .deliver $p:term)   => `(rdsl_pat| .inl (.inl (.inr $p)))
  | `(rdsl_pat| .inject $p:term)    => `(rdsl_pat| .inl (.inr $p))
  | `(rdsl_pat| .corrupt $p:term)   => `(rdsl_pat| .inr $p)

/-! ## Lifting `Expr` and `Comp` across `Ops.sum` -/

section LiftOpsSum

variable {S : Sig} {O₁ O₂ : Ops S}

def _root_.ReductionDsl.Expr.liftL {Γ : List (Ty S)} {t : Ty S} :
    Expr O₁ Γ t → Expr (O₁.sum O₂) Γ t
  | .var v => .var v
  | .unit => .unit
  | .bool b => .bool b
  | .nat n => .nat n
  | .add a b => .add a.liftL b.liftL
  | .sub a b => .sub a.liftL b.liftL
  | .mulK k a => .mulK k a.liftL
  | .divK k a => .divK k a.liftL
  | .modK k a => .modK k a.liftL
  | .lt a b => .lt a.liftL b.liftL
  | .eqN a b => .eqN a.liftL b.liftL
  | .not a => .not a.liftL
  | .and a b => .and a.liftL b.liftL
  | .ite c th el => .ite c.liftL th.liftL el.liftL
  | .pair a b => .pair a.liftL b.liftL
  | .fst a => .fst a.liftL
  | .snd a => .snd a.liftL
  | .inl a => .inl a.liftL
  | .inr a => .inr a.liftL
  | .none => .none
  | .some a => .some a.liftL
  | .caseOpt a n s => .caseOpt a.liftL n.liftL s.liftL
  | .caseSum a l r => .caseSum a.liftL l.liftL r.liftL
  | .letE a b => .letE a.liftL b.liftL
  | .op o a => Expr.op (O := O₁.sum O₂) (Sum.inl o) (a.liftL (t := O₁.dom o))
  | .nil => .nil
  | .cons h tl => .cons h.liftL tl.liftL
  | .len l => .len l.liftL
  | .take n l => .take n.liftL l.liftL
  | .appendL K a b => .appendL K a.liftL b.liftL
  | .findB K l p => .findB K l.liftL p.liftL
  | .anyB K l p => .anyB K l.liftL p.liftL
  | .mapB K l f => .mapB K l.liftL f.liftL
  | .foldrB K l z step => .foldrB K l.liftL z.liftL step.liftL
  | .tconst v => .tconst v.liftL
  | .tget m i => .tget m.liftL i.liftL
  | .tset m i v => .tset m.liftL i.liftL v.liftL

@[simp] theorem _root_.ReductionDsl.Ops.sum_eval_inl (o : O₁.Op) (x : (O₁.dom o).denote) :
    (O₁.sum O₂).eval (Sum.inl o) x = O₁.eval o x := rfl

@[simp] theorem _root_.ReductionDsl.Ops.sum_cost_inl (o : O₁.Op) :
    (O₁.sum O₂).cost (Sum.inl o) = O₁.cost o := rfl

@[simp] theorem _root_.ReductionDsl.Expr.eval_liftL {Γ : List (Ty S)} {t : Ty S}
    (e : Expr O₁ Γ t) (ρ : Env Γ) :
    (e.liftL (O₂ := O₂)).eval ρ = e.eval ρ := by
  induction e with
  | op o a ih =>
    change O₁.eval o (a.liftL.eval ρ) = O₁.eval o (a.eval ρ)
    rw [ih]
  | _ => simp [Expr.liftL, Expr.eval, *]

@[simp] theorem _root_.ReductionDsl.Expr.cost_liftL {Γ : List (Ty S)} {t : Ty S}
    (e : Expr O₁ Γ t) :
    (e.liftL (O₂ := O₂)).cost = e.cost := by
  induction e with
  | op o a ih =>
    change a.liftL.cost + O₁.cost o = a.cost + O₁.cost o
    rw [ih]
  | _ => simp [Expr.liftL, Expr.cost, *]

def _root_.ReductionDsl.Comp.liftL
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {t : Ty S} :
    Comp O₁ I Γ t → Comp (O₁.sum O₂) I Γ t
  | .ret e => .ret e.liftL
  | .bind m k => .bind m.liftL k.liftL
  | .ite c th el => .ite c.liftL th.liftL el.liftL
  | .caseOpt e n s => .caseOpt e.liftL n.liftL s.liftL
  | .caseSum e l r => .caseSum e.liftL l.liftL r.liftL
  | .sample s a => .sample s a.liftL
  | .query g a => .query g a.liftL
  | .iter N s step => .iter N s.liftL step.liftL
  | .findM K l p => .findM K l.liftL p.liftL
  | .anyM K l p => .anyM K l.liftL p.liftL
  | .mapM K l f => .mapM K l.liftL f.liftL
  | .consumeFirstM K l p mark => .consumeFirstM K l.liftL p.liftL mark.liftL
  | .foldM K l z f => .foldM K l.liftL z.liftL f.liftL

@[simp] theorem _root_.ReductionDsl.Comp.eval_liftL {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {t : Ty S} (c : Comp O₁ I Γ t) (ρ : Env Γ) :
    (c.liftL (O₂ := O₂)).eval ρ = c.eval ρ := by
  induction c with
  | ret e => simp [Comp.liftL, Comp.eval]
  | bind m k ihm ihk =>
    simp only [Comp.liftL, Comp.eval, ihm]
    exact bind_congr fun x => ihk (Env.cons x ρ)
  | ite c th el ihth ihel =>
    simp only [Comp.liftL, Comp.eval, Expr.eval_liftL]
    split <;> [exact ihth ρ; exact ihel ρ]
  | caseOpt e n s ihn ihs =>
    simp only [Comp.liftL, Comp.eval, Expr.eval_liftL]
    cases e.eval ρ <;> [exact ihn ρ; exact ihs _]
  | caseSum e l r ihl ihr =>
    simp only [Comp.liftL, Comp.eval, Expr.eval_liftL]
    cases e.eval ρ <;> [exact ihl _; exact ihr _]
  | sample s a => simp [Comp.liftL, Comp.eval]
  | query g a =>
    simp only [Comp.liftL, Comp.eval]
    rw [Expr.eval_liftL]
  | iter N s step ih =>
    simp only [Comp.liftL, Comp.eval, Expr.eval_liftL]
    have hstep : (fun a => (step.liftL (O₂ := O₂)).eval (.cons a ρ)) =
        fun a => step.eval (.cons a ρ) := funext fun a => ih (.cons a ρ)
    rw [hstep]
  | findM K l p ih =>
    simp only [Comp.liftL, Comp.eval, Expr.eval_liftL]
    have hp : (fun x => (p.liftL (O₂ := O₂)).eval (.cons x ρ)) =
        fun x => p.eval (.cons x ρ) := funext fun x => ih (.cons x ρ)
    rw [hp]
  | anyM K l p ih =>
    simp only [Comp.liftL, Comp.eval, Expr.eval_liftL]
    have hp : (fun x => (p.liftL (O₂ := O₂)).eval (.cons x ρ)) =
        fun x => p.eval (.cons x ρ) := funext fun x => ih (.cons x ρ)
    rw [hp]
  | mapM K l f ih =>
    simp only [Comp.liftL, Comp.eval, Expr.eval_liftL]
    have hf : (fun x => (f.liftL (O₂ := O₂)).eval (.cons x ρ)) =
        fun x => f.eval (.cons x ρ) := funext fun x => ih (.cons x ρ)
    rw [hf]
  | consumeFirstM K l p mark ih =>
    simp only [Comp.liftL, Comp.eval, Expr.eval_liftL]
    have hp : (fun x => (p.liftL (O₂ := O₂)).eval (.cons x ρ)) =
        fun x => p.eval (.cons x ρ) := funext fun x => ih (.cons x ρ)
    rw [hp]
  | foldM K l z f ih =>
    simp only [Comp.liftL, Comp.eval, Expr.eval_liftL]
    have hf : (fun x acc => (f.liftL (O₂ := O₂)).eval (.cons x (.cons acc ρ))) =
        fun x acc => f.eval (.cons x (.cons acc ρ)) :=
      funext fun x => funext fun acc => ih (.cons x (.cons acc ρ))
    rw [hf]

@[simp] theorem _root_.ReductionDsl.Comp.cost_liftL {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {t : Ty S} (c : Comp O₁ I Γ t) :
    (c.liftL (O₂ := O₂)).cost = c.cost := by
  induction c <;> simp [Comp.liftL, Comp.cost, *]

@[simp] theorem _root_.ReductionDsl.Comp.queries_liftL {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    {Γ : List (Ty S)} {t : Ty S} (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (c : Comp O₁ I Γ t) :
    (c.liftL (O₂ := O₂)).queries w ws = c.queries w ws := by
  induction c <;> simp [Comp.liftL, Comp.queries, *]

end LiftOpsSum

/-! ## Size honesty for E2E operation and sampler tables -/

section SizeHonest

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] {PQC : Type} [SampleableType PQC]
  (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
  (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (s : BitVec 256)

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem e2eSmOps_sizeHonest : OpsSizeHonest (spkLeakSessionSmOps P ℓ decT encT) :=
  smOps_sizeHonest _ _ _ _ _ _ _ _ _

omit [SampleableType PQC] in
theorem e2eOps_sizeHonest : OpsSizeHonest (spkLeakOps P ℓ Dh encPt encT decT s) := by
  intro o x B hx
  cases o with
  | basePt => simp [Ty.Fits]
  | dh => simp [Ty.Fits]
  | isZeroPt => trivial
  | eqPt => trivial
  | zeroBv => simp [Ty.Fits]
  | spkSc => simp [Ty.Fits]
  | rootExpand => simp [Ty.Fits]
  | extractTag => simp [Ty.Fits]
  | rootCreateChain =>
    rcases x with ⟨rk, pkBytes, rc⟩
    simp only [spkLeakOps]
    rcases bytesToPk? pkBytes with _ | pk
    · trivial
    · dsimp only
      rcases rootCreateChain P.C rk pk (KeyPair.generate P.C rc).privateKey with _ | ⟨rk', ck⟩
      · trivial
      · simp [Ty.Fits]
  | genPub => simp [Ty.Fits]
  | encT => simp [Ty.Fits]
  | decT =>
    simp only [spkLeakOps]
    rcases (bytesToPk? x).bind decT with _ | T
    · trivial
    · simp [Ty.Fits]
  | eqBytes => trivial
  | parseSenderKey =>
    simp only [spkLeakOps]
    rcases SignalMessage.tryFrom P.codec x with _ | msg
    · trivial
    · simp [Ty.Fits]
  | stParty => trivial
  | stEpoch B_idx =>
    simp only [Ty.Fits]
    have hb1 : 1 ≤ bits B_idx := one_le_bits B_idx
    have ht : bits (min x.epoch B_idx) ≤ bits B_idx := bits_mono (Nat.min_le_right _ _)
    omega
  | hasEpoch0Chain => trivial
  | hasSenderChain => trivial
  | hasRecvChain => trivial
  | newSession => simp [Ty.Fits]
  | setPendingPreKey => simp [Ty.Fits]
  | setRootKey => simp [Ty.Fits]
  | setSenderChain => simp [Ty.Fits]
  | addRecvChain => simp [Ty.Fits]
  | resetEpoch0 => simp [Ty.Fits]
  | advancePrevCounter => simp [Ty.Fits]
  | pushRecvChain => simp [Ty.Fits]
  | tryDecryptWhisper B_idx =>
    rcases x with ⟨g, c, rc⟩
    simp only [spkLeakOps]
    rcases SignalMessage.tryFrom P.codec c with _ | msg
    · trivial
    · dsimp only
      rcases SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper
          rc g.session with ⟨_ | m, s_out⟩
      · trivial
      · simp only [Ty.Fits, spkLeakSessionSig, smSig]
        have hb1 : 1 ≤ bits B_idx := one_le_bits B_idx
        have ht : bits (min g.epoch B_idx) ≤ bits B_idx := bits_mono (Nat.min_le_right _ _)
        have hi : bits (min (msg.counter.toNat + 1) B_idx) ≤ bits B_idx :=
          bits_mono (Nat.min_le_right _ _)
        exact ⟨by omega, ⟨by omega, ⟨by omega, by omega⟩⟩⟩

omit [SampleableType PQC] in
theorem e2eFullOps_sizeHonest : OpsSizeHonest (spkLeakSessionOps P ℓ Dh encPt encT decT s) :=
  OpsSizeHonest.sum (e2eSmOps_sizeHonest P ℓ encT decT)
    (e2eOps_sizeHonest P ℓ Dh encPt encT decT s)

omit [DecidableEq Pt] [Zero Pt] in
theorem e2ePrfSamp_sizeHonest : SampSizeHonest (e2ePrfIface Pt ℓ PQC).smp :=
  SampSizeHonest.sum SampSizeHonest.empty
    (SampSizeHonest.unifSamplers (S := spkLeakSessionSig Pt ℓ PQC) e2eUnifSort (fun _ => 1))

omit [DecidableEq Pt] [Zero Pt] in
theorem e2ePrgSamp_sizeHonest : SampSizeHonest (e2ePrgIface Pt ℓ PQC).smp :=
  SampSizeHonest.sum SampSizeHonest.empty
    (SampSizeHonest.unifSamplers (S := spkLeakSessionSig Pt ℓ PQC) e2eUnifSort (fun _ => 1))

end SizeHonest

/-! ## Step helpers, operation wrappers, and `spkLeakRedProg` -/

@[simp] theorem bytesToPk?_pkToBytes (pk : PublicKey) :
    bytesToPk? (pkToBytes pk) = some pk := by
  rcases pk with ⟨⟨bs, h⟩⟩
  simp [pkToBytes, bytesToPk?, h]

@[simp] theorem pkToBytes_beq (pk₁ pk₂ : PublicKey) :
    (pkToBytes pk₁ == pkToBytes pk₂) = (pk₁ == pk₂) := by
  rcases pk₁ with ⟨⟨bs₁, h₁⟩⟩
  rcases pk₂ with ⟨⟨bs₂, h₂⟩⟩
  by_cases h : bs₁ = bs₂
  · subst h; simp [pkToBytes]
  · have hne : (⟨⟨bs₁, h₁⟩⟩ : PublicKey) ≠ ⟨⟨bs₂, h₂⟩⟩ := fun heq => by cases heq; exact h rfl
    simp [pkToBytes, beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr hne]

@[simp] theorem pkToBytes_inj (pk₁ pk₂ : PublicKey) :
    pkToBytes pk₁ = pkToBytes pk₂ ↔ pk₁ = pk₂ := by
  rcases pk₁ with ⟨⟨bs₁, h₁⟩⟩
  rcases pk₂ with ⟨⟨bs₂, h₂⟩⟩
  constructor <;> (intro h; cases h; rfl)

theorem rootCreateChain_index_zero (C : Crypto) (rk : BitVec 256)
    (their : PublicKey) (our : PrivateKey) (rk' : BitVec 256)
    (ck : LibsignalSession.ChainKey)
    (h : rootCreateChain C rk their our = .ok (rk', ck)) :
    (⟨ck.key, 0⟩ : LibsignalSession.ChainKey) = ck := by
  unfold rootCreateChain at h
  rcases hcr : Ratchet.createChain C.F C.X rk their.bytes our.bytes with _ | ⟨rk₁, k₁⟩ <;>
    simp [hcr] at h
  rcases h with ⟨_, rfl⟩
  rfl

@[simp] theorem evictReceiverChains_singleton (x : ReceiverChain) :
    RatchetState.evictReceiverChains [x] = [x] := rfl

def e2eInitA {PQC : Type} (P : Params Bytes PQC)
    (args : BitVec 256 × BitVec 256 × BitVec 256 × BitVec 256 × BitVec 256 × BitVec 256) :
    GhostState Bytes :=
  let (rk1, ck0, spkSc, alice, pqr, ck1) := args
  let spk := (KeyPair.generate P.C spkSc).publicKey
  let sendingRatchetKey := KeyPair.generate P.C alice
  let sess := ((SessionState.new currentVersion P.idA P.idB rk1
    (P.spqr.init .a2b pqr)).addReceiverChain spk ⟨ck0, 0⟩).setSenderChain
    sendingRatchetKey ⟨ck1, 0⟩
  ⟨.A, sess.setUnacknowledgedPreKeyMessage, 0, [0]⟩

def e2eInitB {PQC : Type} (P : Params Bytes PQC)
    (args : BitVec 256 × BitVec 256 × BitVec 256 × BitVec 256 × BitVec 256) :
    GhostState Bytes :=
  let (rk, ck0, spkSc, alice, pqr) := args
  P.initB ⟨rk, ck0, spkSc, alice, pqr⟩

def senderKeyPt {Pt : Type} [DecidableEq Pt] [Zero Pt] {PQC : Type} (P : Params Bytes PQC)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (c : Bytes) : Option Pt :=
  match SignalMessage.tryFrom P.codec c with
  | .error _ => none
  | .ok msg =>
    match decT msg.senderRatchetKey with
    | none => none
    | some T =>
      if T = 0 ∨ encT T ≠ msg.senderRatchetKey then none else some T

def finishRecvB0 {PQC : Type} (P : Params Bytes PQC) (ℓ : ℕ)
    (g : GhostState Bytes) (c : Bytes) (rc prk : BitVec 256) :
    Option (GhostState Bytes × ℕ × ℕ × CBC.Plain ℓ) :=
  match SignalMessage.tryFrom P.codec c with
  | .error _ => none
  | .ok msg =>
    let (rk1, ck1) := (expandPRG P.C.F).gen prk
    match rootCreateChain P.C rk1 msg.senderRatchetKey
        (KeyPair.generate P.C rc).privateKey with
    | .error _ => none
    | .ok (rk2, ck2) =>
      let sess' : SessionState Bytes :=
        { g.session with
          previousCounter := 0
          rootKey := rk2
          receiverChains := [⟨msg.senderRatchetKey, some ⟨ck1, 0⟩, []⟩]
          senderChain := some ⟨KeyPair.generate P.C rc, ck2⟩ }
      match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper
          rc sess' with
      | (.error _, _) => none
      | (.ok m, s_out) =>
        let epochs := ([1] : List ℕ).drop (1 - s_out.receiverChains.length)
        some ({ g with session := s_out, epoch := 1, chainEpochs := epochs },
          1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m)

def needsDH {PQC : Type} (P : Params Bytes PQC) (g : GhostState Bytes) (c : Bytes) : Bool :=
  match SignalMessage.tryFrom P.codec c with
  | .error _ => false
  | .ok msg =>
    (g.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)).isNone

def dhTargetPt {Pt : Type} [DecidableEq Pt] [Zero Pt] {PQC : Type} (P : Params Bytes PQC)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (g : GhostState Bytes) (c : Bytes) : Option Pt :=
  match SignalMessage.tryFrom P.codec c with
  | .error _ => none
  | .ok msg =>
    match decT msg.senderRatchetKey with
    | none => none
    | some T =>
      if T = 0 ∨ encT T ≠ msg.senderRatchetKey then none
      else match g.session.senderChain with
        | none => none
        | some _ => some T

def sendHalfReal {PQC : Type} (P : Params Bytes PQC) (rkM : BitVec 256) (c : Bytes)
    (rc : BitVec 256) : Option (BitVec 256 × BitVec 256) :=
  match SignalMessage.tryFrom P.codec c with
  | .error _ => none
  | .ok msg =>
    match rootCreateChain P.C rkM msg.senderRatchetKey
        (KeyPair.generate P.C rc).privateKey with
    | .error _ => none
    | .ok (rk', ck) => some (rk', ck.key)

def finishHop2DH {PQC : Type} (P : Params Bytes PQC) (ℓ : ℕ)
    (g : GhostState Bytes) (c : Bytes) (rc rk2 ckR ckS : BitVec 256) :
    Option (GhostState Bytes × ℕ × ℕ × CBC.Plain ℓ) :=
  match SignalMessage.tryFrom P.codec c with
  | .error _ => none
  | .ok msg =>
    match g.session.senderChain with
    | none => none
    | some sc =>
      let newKey := KeyPair.generate P.C rc
      let cur := sc.chainKey.index
      let sess' : SessionState Bytes :=
        { g.session with
          previousCounter := if cur = 0 then 0 else cur - 1
          rootKey := rk2
          receiverChains := RatchetState.evictReceiverChains
            (g.session.receiverChains ++ [⟨msg.senderRatchetKey, some ⟨ckR, 0⟩, []⟩])
          senderChain := some ⟨newKey, ⟨ckS, 0⟩⟩ }
      match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs g.party) msg .whisper
          rc sess' with
      | (.error _, _) => none
      | (.ok m, s_out) =>
        let epochs := (g.chainEpochs ++ [g.epoch + 1]).drop
          ((g.chainEpochs.length + 1) - s_out.receiverChains.length)
        some ({ g with session := s_out, epoch := g.epoch + 1, chainEpochs := epochs },
          g.epoch + 1, msg.counter.toNat + 1, padOrTruncatePlain ℓ m)

section SpkLeakRedProg

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] {PQC : Type}
  (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
  (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (s : BitVec 256) (K B qep : ℕ)

local notation "S" => spkLeakSessionSig Pt ℓ PQC
local notation "OSM" => spkLeakSessionSmOps P ℓ decT encT
local notation "OO" => spkLeakSessionOps P ℓ Dh encPt encT decT s
local notation "II" => e2ePrfIface Pt ℓ PQC
local notation "GS" => @gsTy Pt (GhostState Bytes) Unit (CBC.Plain ℓ) PQC (BitVec 256) Bytes
local notation "RR" => @smRrTy Pt (GhostState Bytes) Unit (CBC.Plain ℓ) PQC (BitVec 256) Bytes

def opReceive {Γ : List (Ty S)} (g : Expr OO Γ (.base .st))
    (c : Expr OO Γ (.base .ct)) (rc : Expr OO Γ (.base .rcoins)) :
    Expr OO Γ (.opt (.prod (.base .st) (.prod .nat (.prod .nat (.base .msg))))) :=
  Expr.op (O := OO) (Sum.inl (.receive B)) (.pair g (.pair c rc))

def opInjOK {Γ : List (Ty S)} (c : Expr OO Γ (.base .ct)) : Expr OO Γ .bool :=
  Expr.op (O := OO) (Sum.inl .injOK) c

def opBasePt {Γ : List (Ty S)} : Expr OO Γ (.base .key) :=
  Expr.op (O := OO) (Sum.inr .basePt) .unit

def opDh {Γ : List (Ty S)} (sc : Expr OO Γ (.base .rcoins))
    (T : Expr OO Γ (.base .key)) : Expr OO Γ (.base .key) :=
  Expr.op (O := OO) (Sum.inr .dh) (.pair sc T)

def opIsZeroPt {Γ : List (Ty S)} (T : Expr OO Γ (.base .key)) : Expr OO Γ .bool :=
  Expr.op (O := OO) (Sum.inr .isZeroPt) T

def opEqPt {Γ : List (Ty S)} (T₁ T₂ : Expr OO Γ (.base .key)) : Expr OO Γ .bool :=
  Expr.op (O := OO) (Sum.inr .eqPt) (.pair T₁ T₂)

def opZeroBv {Γ : List (Ty S)} : Expr OO Γ (.base .rcoins) :=
  Expr.op (O := OO) (Sum.inr .zeroBv) .unit

def opSpkSc {Γ : List (Ty S)} : Expr OO Γ (.base .rcoins) :=
  Expr.op (O := OO) (Sum.inr .spkSc) .unit

def opRootExpand {Γ : List (Ty S)} (prk : Expr OO Γ (.base .rcoins)) :
    Expr OO Γ (.prod (.base .rcoins) (.base .rcoins)) :=
  Expr.op (O := OO) (Sum.inr .rootExpand) prk

def opExtractTag {Γ : List (Ty S)} (rk : Expr OO Γ (.base .rcoins))
    (T : Expr OO Γ (.base .key)) : Expr OO Γ (.base .rcoins) :=
  Expr.op (O := OO) (Sum.inr .extractTag) (.pair rk T)

def opRootCreateChain {Γ : List (Ty S)} (rk : Expr OO Γ (.base .rcoins))
    (pkBytes : Expr OO Γ (.base .ct)) (rc : Expr OO Γ (.base .rcoins)) :
    Expr OO Γ (.opt (.prod (.base .rcoins) (.base .rcoins))) :=
  Expr.op (O := OO) (Sum.inr .rootCreateChain) (.pair rk (.pair pkBytes rc))

def opGenPub {Γ : List (Ty S)} (sc : Expr OO Γ (.base .rcoins)) : Expr OO Γ (.base .ct) :=
  Expr.op (O := OO) (Sum.inr .genPub) sc

def opEncT {Γ : List (Ty S)} (T : Expr OO Γ (.base .key)) : Expr OO Γ (.base .ct) :=
  Expr.op (O := OO) (Sum.inr .encT) T

def opDecT {Γ : List (Ty S)} (bs : Expr OO Γ (.base .ct)) : Expr OO Γ (.opt (.base .key)) :=
  Expr.op (O := OO) (Sum.inr .decT) bs

def opEqBytes {Γ : List (Ty S)} (a b : Expr OO Γ (.base .ct)) : Expr OO Γ .bool :=
  Expr.op (O := OO) (Sum.inr .eqBytes) (.pair a b)

def opParseSenderKey {Γ : List (Ty S)} (c : Expr OO Γ (.base .ct)) :
    Expr OO Γ (.opt (.base .ct)) :=
  Expr.op (O := OO) (Sum.inr .parseSenderKey) c

def opStParty {Γ : List (Ty S)} (g : Expr OO Γ (.base .st)) : Expr OO Γ .bool :=
  Expr.op (O := OO) (Sum.inr .stParty) g

def opStEpoch {Γ : List (Ty S)} (g : Expr OO Γ (.base .st)) : Expr OO Γ .nat :=
  Expr.op (O := OO) (Sum.inr (.stEpoch B)) g

def opHasEpoch0Chain {Γ : List (Ty S)} (g : Expr OO Γ (.base .st)) : Expr OO Γ .bool :=
  Expr.op (O := OO) (Sum.inr .hasEpoch0Chain) g

def opHasSenderChain {Γ : List (Ty S)} (g : Expr OO Γ (.base .st)) : Expr OO Γ .bool :=
  Expr.op (O := OO) (Sum.inr .hasSenderChain) g

def opHasRecvChain {Γ : List (Ty S)} (g : Expr OO Γ (.base .st))
    (pkBytes : Expr OO Γ (.base .ct)) : Expr OO Γ .bool :=
  Expr.op (O := OO) (Sum.inr .hasRecvChain) (.pair g pkBytes)

def opNewSession {Γ : List (Ty S)} (isB : Expr OO Γ .bool)
    (rk pqr : Expr OO Γ (.base .rcoins)) : Expr OO Γ (.base .st) :=
  Expr.op (O := OO) (Sum.inr .newSession) (.pair isB (.pair rk pqr))

def opSetPendingPreKey {Γ : List (Ty S)} (g : Expr OO Γ (.base .st)) : Expr OO Γ (.base .st) :=
  Expr.op (O := OO) (Sum.inr .setPendingPreKey) g

def opSetRootKey {Γ : List (Ty S)} (g : Expr OO Γ (.base .st))
    (rk : Expr OO Γ (.base .rcoins)) : Expr OO Γ (.base .st) :=
  Expr.op (O := OO) (Sum.inr .setRootKey) (.pair g rk)

def opSetSenderChain {Γ : List (Ty S)} (g : Expr OO Γ (.base .st))
    (sc ck : Expr OO Γ (.base .rcoins)) : Expr OO Γ (.base .st) :=
  Expr.op (O := OO) (Sum.inr .setSenderChain) (.pair g (.pair sc ck))

def opAddRecvChain {Γ : List (Ty S)} (g : Expr OO Γ (.base .st))
    (pkBytes : Expr OO Γ (.base .ct)) (ck : Expr OO Γ (.base .rcoins)) :
    Expr OO Γ (.base .st) :=
  Expr.op (O := OO) (Sum.inr .addRecvChain) (.pair g (.pair pkBytes ck))

def opResetEpoch0 {Γ : List (Ty S)} (g : Expr OO Γ (.base .st)) : Expr OO Γ (.base .st) :=
  Expr.op (O := OO) (Sum.inr .resetEpoch0) g

def opAdvancePrevCounter {Γ : List (Ty S)} (g : Expr OO Γ (.base .st)) : Expr OO Γ (.base .st) :=
  Expr.op (O := OO) (Sum.inr .advancePrevCounter) g

def opPushRecvChain {Γ : List (Ty S)} (g : Expr OO Γ (.base .st))
    (pkBytes : Expr OO Γ (.base .ct)) (ck : Expr OO Γ (.base .rcoins)) :
    Expr OO Γ (.base .st) :=
  Expr.op (O := OO) (Sum.inr .pushRecvChain) (.pair g (.pair pkBytes ck))

def opTryDecryptWhisper {Γ : List (Ty S)} (g : Expr OO Γ (.base .st))
    (c : Expr OO Γ (.base .ct)) (rc : Expr OO Γ (.base .rcoins)) :
    Expr OO Γ (.opt (.prod (.base .st) (.prod .nat (.prod .nat (.base .msg))))) :=
  Expr.op (O := OO) (Sum.inr (.tryDecryptWhisper B)) (.pair g (.pair c rc))

@[simp] theorem opReceive_eval {Γ : List (Ty S)} (g : Expr OO Γ (.base .st))
    (c : Expr OO Γ (.base .ct)) (rc : Expr OO Γ (.base .rcoins)) (ρ : Env Γ) :
    (opReceive P ℓ Dh encPt encT decT s B g c rc).eval ρ =
      ((sessionSchemeU P ℓ).receive (g.eval ρ) (c.eval ρ) (rc.eval ρ)).map
        (fun (st', t', i', m') => (st', min t' B, min i' B, m')) := rfl

@[simp] theorem opReceive_cost {Γ : List (Ty S)} (g : Expr OO Γ (.base .st))
    (c : Expr OO Γ (.base .ct)) (rc : Expr OO Γ (.base .rcoins)) :
    (opReceive P ℓ Dh encPt encT decT s B g c rc).cost =
      g.cost + (c.cost + rc.cost + 1) + 1 + bits B := rfl

@[simp] theorem opInjOK_eval {Γ : List (Ty S)} (c : Expr OO Γ (.base .ct)) (ρ : Env Γ) :
    (opInjOK P ℓ Dh encPt encT decT s c).eval ρ =
      ratchetKeyAdmissible protoSignalCodec decT encT (c.eval ρ) := rfl

@[simp] theorem opInjOK_cost {Γ : List (Ty S)} (c : Expr OO Γ (.base .ct)) :
    (opInjOK P ℓ Dh encPt encT decT s c).cost = c.cost + 1 := rfl

@[simp] theorem opBasePt_eval {Γ : List (Ty S)} (ρ : Env Γ) :
    (opBasePt P ℓ Dh encPt encT decT s (Γ := Γ)).eval ρ = Dh.base := rfl

@[simp] theorem opBasePt_cost {Γ : List (Ty S)} :
    (opBasePt P ℓ Dh encPt encT decT s (Γ := Γ)).cost = 2 := rfl

@[simp] theorem opDh_eval {Γ : List (Ty S)} (sc : Expr OO Γ (.base .rcoins))
    (T : Expr OO Γ (.base .key)) (ρ : Env Γ) :
    (opDh P ℓ Dh encPt encT decT s sc T).eval ρ = Dh.dh (sc.eval ρ) (T.eval ρ) := rfl

@[simp] theorem opDh_cost {Γ : List (Ty S)} (sc : Expr OO Γ (.base .rcoins))
    (T : Expr OO Γ (.base .key)) :
    (opDh P ℓ Dh encPt encT decT s sc T).cost = sc.cost + T.cost + 1 + 1 := rfl

@[simp] theorem opIsZeroPt_eval {Γ : List (Ty S)} (T : Expr OO Γ (.base .key)) (ρ : Env Γ) :
    (opIsZeroPt P ℓ Dh encPt encT decT s T).eval ρ = (T.eval ρ == 0) := rfl

@[simp] theorem opIsZeroPt_cost {Γ : List (Ty S)} (T : Expr OO Γ (.base .key)) :
    (opIsZeroPt P ℓ Dh encPt encT decT s T).cost = T.cost + 1 := rfl

@[simp] theorem opEqPt_eval {Γ : List (Ty S)} (T₁ T₂ : Expr OO Γ (.base .key)) (ρ : Env Γ) :
    (opEqPt P ℓ Dh encPt encT decT s T₁ T₂).eval ρ = (T₁.eval ρ == T₂.eval ρ) := rfl

@[simp] theorem opEqPt_cost {Γ : List (Ty S)} (T₁ T₂ : Expr OO Γ (.base .key)) :
    (opEqPt P ℓ Dh encPt encT decT s T₁ T₂).cost = T₁.cost + T₂.cost + 1 + 1 := rfl

@[simp] theorem opZeroBv_eval {Γ : List (Ty S)} (ρ : Env Γ) :
    (opZeroBv P ℓ Dh encPt encT decT s (Γ := Γ)).eval ρ = 0 := rfl

@[simp] theorem opZeroBv_cost {Γ : List (Ty S)} :
    (opZeroBv P ℓ Dh encPt encT decT s (Γ := Γ)).cost = 2 := rfl

@[simp] theorem opSpkSc_eval {Γ : List (Ty S)} (ρ : Env Γ) :
    (opSpkSc P ℓ Dh encPt encT decT s (Γ := Γ)).eval ρ = s := rfl

@[simp] theorem opSpkSc_cost {Γ : List (Ty S)} :
    (opSpkSc P ℓ Dh encPt encT decT s (Γ := Γ)).cost = 2 := rfl

@[simp] theorem opRootExpand_eval {Γ : List (Ty S)} (prk : Expr OO Γ (.base .rcoins))
    (ρ : Env Γ) :
    (opRootExpand P ℓ Dh encPt encT decT s prk).eval ρ =
      (expandPRG P.C.F).gen (prk.eval ρ) := rfl

@[simp] theorem opRootExpand_cost {Γ : List (Ty S)} (prk : Expr OO Γ (.base .rcoins)) :
    (opRootExpand P ℓ Dh encPt encT decT s prk).cost = prk.cost + 1 := rfl

@[simp] theorem opExtractTag_eval {Γ : List (Ty S)} (rk : Expr OO Γ (.base .rcoins))
    (T : Expr OO Γ (.base .key)) (ρ : Env Γ) :
    (opExtractTag P ℓ Dh encPt encT decT s rk T).eval ρ =
      (extractPRF P.C.F encPt).tag (rk.eval ρ) (T.eval ρ) := rfl

@[simp] theorem opExtractTag_cost {Γ : List (Ty S)} (rk : Expr OO Γ (.base .rcoins))
    (T : Expr OO Γ (.base .key)) :
    (opExtractTag P ℓ Dh encPt encT decT s rk T).cost = rk.cost + T.cost + 1 + 1 := rfl

@[simp] theorem opRootCreateChain_eval {Γ : List (Ty S)} (rk : Expr OO Γ (.base .rcoins))
    (pkBytes : Expr OO Γ (.base .ct)) (rc : Expr OO Γ (.base .rcoins)) (ρ : Env Γ) :
    (opRootCreateChain P ℓ Dh encPt encT decT s rk pkBytes rc).eval ρ =
      match bytesToPk? (pkBytes.eval ρ) with
      | none => none
      | some pk =>
        match rootCreateChain P.C (rk.eval ρ) pk
            (KeyPair.generate P.C (rc.eval ρ)).privateKey with
        | .error _ => none
        | .ok (rk', ck) => some (rk', ck.key) := rfl

@[simp] theorem opRootCreateChain_cost {Γ : List (Ty S)} (rk : Expr OO Γ (.base .rcoins))
    (pkBytes : Expr OO Γ (.base .ct)) (rc : Expr OO Γ (.base .rcoins)) :
    (opRootCreateChain P ℓ Dh encPt encT decT s rk pkBytes rc).cost =
      rk.cost + (pkBytes.cost + rc.cost + 1) + 1 + 1 := rfl

@[simp] theorem opGenPub_eval {Γ : List (Ty S)} (sc : Expr OO Γ (.base .rcoins)) (ρ : Env Γ) :
    (opGenPub P ℓ Dh encPt encT decT s sc).eval ρ =
      pkToBytes (KeyPair.generate P.C (sc.eval ρ)).publicKey := rfl

@[simp] theorem opGenPub_cost {Γ : List (Ty S)} (sc : Expr OO Γ (.base .rcoins)) :
    (opGenPub P ℓ Dh encPt encT decT s sc).cost = sc.cost + 1 := rfl

@[simp] theorem opEncT_eval {Γ : List (Ty S)} (T : Expr OO Γ (.base .key)) (ρ : Env Γ) :
    (opEncT P ℓ Dh encPt encT decT s T).eval ρ = pkToBytes (encT (T.eval ρ)) := rfl

@[simp] theorem opEncT_cost {Γ : List (Ty S)} (T : Expr OO Γ (.base .key)) :
    (opEncT P ℓ Dh encPt encT decT s T).cost = T.cost + 1 := rfl

@[simp] theorem opDecT_eval {Γ : List (Ty S)} (bs : Expr OO Γ (.base .ct)) (ρ : Env Γ) :
    (opDecT P ℓ Dh encPt encT decT s bs).eval ρ =
      (bytesToPk? (bs.eval ρ)).bind decT := rfl

@[simp] theorem opDecT_cost {Γ : List (Ty S)} (bs : Expr OO Γ (.base .ct)) :
    (opDecT P ℓ Dh encPt encT decT s bs).cost = bs.cost + 1 := rfl

@[simp] theorem opEqBytes_eval {Γ : List (Ty S)} (a b : Expr OO Γ (.base .ct)) (ρ : Env Γ) :
    (opEqBytes P ℓ Dh encPt encT decT s a b).eval ρ =
      ((a.eval ρ : Bytes) == (b.eval ρ : Bytes)) := rfl

@[simp] theorem opEqBytes_cost {Γ : List (Ty S)} (a b : Expr OO Γ (.base .ct)) :
    (opEqBytes P ℓ Dh encPt encT decT s a b).cost = a.cost + b.cost + 1 + 1 := rfl

@[simp] theorem opParseSenderKey_eval {Γ : List (Ty S)} (c : Expr OO Γ (.base .ct)) (ρ : Env Γ) :
    (opParseSenderKey P ℓ Dh encPt encT decT s c).eval ρ =
      match SignalMessage.tryFrom P.codec (c.eval ρ) with
      | .error _ => none
      | .ok msg => some (pkToBytes msg.senderRatchetKey) := rfl

@[simp] theorem opParseSenderKey_cost {Γ : List (Ty S)} (c : Expr OO Γ (.base .ct)) :
    (opParseSenderKey P ℓ Dh encPt encT decT s c).cost = c.cost + 1 := rfl

@[simp] theorem opStParty_eval {Γ : List (Ty S)} (g : Expr OO Γ (.base .st)) (ρ : Env Γ) :
    (opStParty P ℓ Dh encPt encT decT s g).eval ρ = partyEnc (g.eval ρ).party := rfl

@[simp] theorem opStParty_cost {Γ : List (Ty S)} (g : Expr OO Γ (.base .st)) :
    (opStParty P ℓ Dh encPt encT decT s g).cost = g.cost + 1 := rfl

@[simp] theorem opStEpoch_eval {Γ : List (Ty S)} (g : Expr OO Γ (.base .st)) (ρ : Env Γ) :
    (opStEpoch P ℓ Dh encPt encT decT s B g).eval ρ = min (g.eval ρ).epoch B := rfl

@[simp] theorem opStEpoch_cost {Γ : List (Ty S)} (g : Expr OO Γ (.base .st)) :
    (opStEpoch P ℓ Dh encPt encT decT s B g).cost = g.cost + bits B := rfl

@[simp] theorem opHasEpoch0Chain_eval {Γ : List (Ty S)} (g : Expr OO Γ (.base .st)) (ρ : Env Γ) :
    (opHasEpoch0Chain P ℓ Dh encPt encT decT s g).eval ρ =
      (g.eval ρ).chainEpochs.contains 0 := rfl

@[simp] theorem opHasEpoch0Chain_cost {Γ : List (Ty S)} (g : Expr OO Γ (.base .st)) :
    (opHasEpoch0Chain P ℓ Dh encPt encT decT s g).cost = g.cost + 1 := rfl

@[simp] theorem opHasSenderChain_eval {Γ : List (Ty S)} (g : Expr OO Γ (.base .st)) (ρ : Env Γ) :
    (opHasSenderChain P ℓ Dh encPt encT decT s g).eval ρ =
      (g.eval ρ).session.senderChain.isSome := rfl

@[simp] theorem opHasSenderChain_cost {Γ : List (Ty S)} (g : Expr OO Γ (.base .st)) :
    (opHasSenderChain P ℓ Dh encPt encT decT s g).cost = g.cost + 1 := rfl

@[simp] theorem opHasRecvChain_eval {Γ : List (Ty S)} (g : Expr OO Γ (.base .st))
    (pkBytes : Expr OO Γ (.base .ct)) (ρ : Env Γ) :
    (opHasRecvChain P ℓ Dh encPt encT decT s g pkBytes).eval ρ =
      match bytesToPk? (pkBytes.eval ρ) with
      | none => false
      | some pk =>
        ((g.eval ρ).session.receiverChains.findIdx? (·.senderRatchetKey == pk)).isSome := rfl

@[simp] theorem opHasRecvChain_cost {Γ : List (Ty S)} (g : Expr OO Γ (.base .st))
    (pkBytes : Expr OO Γ (.base .ct)) :
    (opHasRecvChain P ℓ Dh encPt encT decT s g pkBytes).cost =
      g.cost + pkBytes.cost + 1 + 1 := rfl

@[simp] theorem opNewSession_eval {Γ : List (Ty S)} (isB : Expr OO Γ .bool)
    (rk pqr : Expr OO Γ (.base .rcoins)) (ρ : Env Γ) :
    (opNewSession P ℓ Dh encPt encT decT s isB rk pqr).eval ρ =
      if isB.eval ρ then
        ⟨.B, SessionState.new currentVersion P.idB P.idA (rk.eval ρ)
          (P.spqr.init .b2a (pqr.eval ρ)), 0, []⟩
      else
        ⟨.A, SessionState.new currentVersion P.idA P.idB (rk.eval ρ)
          (P.spqr.init .a2b (pqr.eval ρ)), 0, []⟩ := rfl

@[simp] theorem opNewSession_cost {Γ : List (Ty S)} (isB : Expr OO Γ .bool)
    (rk pqr : Expr OO Γ (.base .rcoins)) :
    (opNewSession P ℓ Dh encPt encT decT s isB rk pqr).cost =
      isB.cost + (rk.cost + pqr.cost + 1) + 1 + 1 := rfl

@[simp] theorem opSetPendingPreKey_eval {Γ : List (Ty S)} (g : Expr OO Γ (.base .st))
    (ρ : Env Γ) :
    (opSetPendingPreKey P ℓ Dh encPt encT decT s g).eval ρ =
      let gv := g.eval ρ
      { gv with session := gv.session.setUnacknowledgedPreKeyMessage } := rfl

@[simp] theorem opSetPendingPreKey_cost {Γ : List (Ty S)} (g : Expr OO Γ (.base .st)) :
    (opSetPendingPreKey P ℓ Dh encPt encT decT s g).cost = g.cost + 1 := rfl

@[simp] theorem opSetRootKey_eval {Γ : List (Ty S)} (g : Expr OO Γ (.base .st))
    (rk : Expr OO Γ (.base .rcoins)) (ρ : Env Γ) :
    (opSetRootKey P ℓ Dh encPt encT decT s g rk).eval ρ =
      let gv := g.eval ρ
      { gv with session := { gv.session with rootKey := rk.eval ρ } } := rfl

@[simp] theorem opSetRootKey_cost {Γ : List (Ty S)} (g : Expr OO Γ (.base .st))
    (rk : Expr OO Γ (.base .rcoins)) :
    (opSetRootKey P ℓ Dh encPt encT decT s g rk).cost = g.cost + rk.cost + 1 + 1 := rfl

@[simp] theorem opSetSenderChain_eval {Γ : List (Ty S)} (g : Expr OO Γ (.base .st))
    (sc ck : Expr OO Γ (.base .rcoins)) (ρ : Env Γ) :
    (opSetSenderChain P ℓ Dh encPt encT decT s g sc ck).eval ρ =
      let gv := g.eval ρ
      { gv with session :=
          gv.session.setSenderChain (KeyPair.generate P.C (sc.eval ρ)) ⟨ck.eval ρ, 0⟩ } := rfl

@[simp] theorem opSetSenderChain_cost {Γ : List (Ty S)} (g : Expr OO Γ (.base .st))
    (sc ck : Expr OO Γ (.base .rcoins)) :
    (opSetSenderChain P ℓ Dh encPt encT decT s g sc ck).cost =
      g.cost + (sc.cost + ck.cost + 1) + 1 + 1 := rfl

@[simp] theorem opAddRecvChain_eval {Γ : List (Ty S)} (g : Expr OO Γ (.base .st))
    (pkBytes : Expr OO Γ (.base .ct)) (ck : Expr OO Γ (.base .rcoins)) (ρ : Env Γ) :
    (opAddRecvChain P ℓ Dh encPt encT decT s g pkBytes ck).eval ρ =
      let gv := g.eval ρ
      match bytesToPk? (pkBytes.eval ρ) with
      | none => gv
      | some pk =>
        { gv with
          session := gv.session.addReceiverChain pk ⟨ck.eval ρ, 0⟩
          chainEpochs := gv.chainEpochs ++ [gv.epoch] } := rfl

@[simp] theorem opAddRecvChain_cost {Γ : List (Ty S)} (g : Expr OO Γ (.base .st))
    (pkBytes : Expr OO Γ (.base .ct)) (ck : Expr OO Γ (.base .rcoins)) :
    (opAddRecvChain P ℓ Dh encPt encT decT s g pkBytes ck).cost =
      g.cost + (pkBytes.cost + ck.cost + 1) + 1 + 1 := rfl

@[simp] theorem opResetEpoch0_eval {Γ : List (Ty S)} (g : Expr OO Γ (.base .st)) (ρ : Env Γ) :
    (opResetEpoch0 P ℓ Dh encPt encT decT s g).eval ρ =
      let gv := g.eval ρ
      { gv with
        session := { gv.session with previousCounter := 0, receiverChains := [] }
        epoch := 0
        chainEpochs := [] } := rfl

@[simp] theorem opResetEpoch0_cost {Γ : List (Ty S)} (g : Expr OO Γ (.base .st)) :
    (opResetEpoch0 P ℓ Dh encPt encT decT s g).cost = g.cost + 1 := rfl

@[simp] theorem opAdvancePrevCounter_eval {Γ : List (Ty S)} (g : Expr OO Γ (.base .st))
    (ρ : Env Γ) :
    (opAdvancePrevCounter P ℓ Dh encPt encT decT s g).eval ρ =
      let gv := g.eval ρ
      let prev := match gv.session.senderChain with
        | none => gv.session.previousCounter
        | some sc => if sc.chainKey.index = 0 then 0 else sc.chainKey.index - 1
      { gv with session := { gv.session with previousCounter := prev } } := rfl

@[simp] theorem opAdvancePrevCounter_cost {Γ : List (Ty S)} (g : Expr OO Γ (.base .st)) :
    (opAdvancePrevCounter P ℓ Dh encPt encT decT s g).cost = g.cost + 1 := rfl

@[simp] theorem opPushRecvChain_eval {Γ : List (Ty S)} (g : Expr OO Γ (.base .st))
    (pkBytes : Expr OO Γ (.base .ct)) (ck : Expr OO Γ (.base .rcoins)) (ρ : Env Γ) :
    (opPushRecvChain P ℓ Dh encPt encT decT s g pkBytes ck).eval ρ =
      let gv := g.eval ρ
      match bytesToPk? (pkBytes.eval ρ) with
      | none => gv
      | some pk =>
        let rcs' := RatchetState.evictReceiverChains
          (gv.session.receiverChains ++ [⟨pk, some ⟨ck.eval ρ, 0⟩, []⟩])
        { gv with
          session := { gv.session with receiverChains := rcs' }
          epoch := gv.epoch + 1
          chainEpochs := gv.chainEpochs ++ [gv.epoch + 1] } := rfl

@[simp] theorem opPushRecvChain_cost {Γ : List (Ty S)} (g : Expr OO Γ (.base .st))
    (pkBytes : Expr OO Γ (.base .ct)) (ck : Expr OO Γ (.base .rcoins)) :
    (opPushRecvChain P ℓ Dh encPt encT decT s g pkBytes ck).cost =
      g.cost + (pkBytes.cost + ck.cost + 1) + 1 + 1 := rfl

@[simp] theorem opTryDecryptWhisper_eval {Γ : List (Ty S)} (g : Expr OO Γ (.base .st))
    (c : Expr OO Γ (.base .ct)) (rc : Expr OO Γ (.base .rcoins)) (ρ : Env Γ) :
    (opTryDecryptWhisper P ℓ Dh encPt encT decT s B g c rc).eval ρ =
      let gv := g.eval ρ
      match SignalMessage.tryFrom P.codec (c.eval ρ) with
      | .error _ => none
      | .ok msg =>
        match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs gv.party) msg .whisper
            (rc.eval ρ) gv.session with
        | (.error _, _) => none
        | (.ok m, s_out) =>
          let epochs := gv.chainEpochs.drop (gv.chainEpochs.length - s_out.receiverChains.length)
          some ({ gv with session := s_out, chainEpochs := epochs },
            min gv.epoch B, min (msg.counter.toNat + 1) B, padOrTruncatePlain ℓ m) := rfl

@[simp] theorem opTryDecryptWhisper_cost {Γ : List (Ty S)} (g : Expr OO Γ (.base .st))
    (c : Expr OO Γ (.base .ct)) (rc : Expr OO Γ (.base .rcoins)) :
    (opTryDecryptWhisper P ℓ Dh encPt encT decT s B g c rc).cost =
      g.cost + (c.cost + rc.cost + 1) + 1 + bits B := rfl

def opInitA {Γ : List (Ty S)}
    (rk1 ck0 spkSc alice pqr ck1 : Expr OO Γ (.base .rcoins)) : Expr OO Γ (.base .st) :=
  opSetPendingPreKey P ℓ Dh encPt encT decT s
    (opSetSenderChain P ℓ Dh encPt encT decT s
      (opAddRecvChain P ℓ Dh encPt encT decT s
        (opNewSession P ℓ Dh encPt encT decT s (.bool false) rk1 pqr)
        (opGenPub P ℓ Dh encPt encT decT s spkSc) ck0)
      alice ck1)

def opInitB {Γ : List (Ty S)}
    (rk ck0 spkSc _alice pqr : Expr OO Γ (.base .rcoins)) : Expr OO Γ (.base .st) :=
  opSetSenderChain P ℓ Dh encPt encT decT s
    (opNewSession P ℓ Dh encPt encT decT s (.bool true) rk pqr)
    spkSc ck0

def opIsB0 {Γ : List (Ty S)} (g : Expr OO Γ (.base .st)) : Expr OO Γ .bool :=
  .letE g
    (.and (opStParty P ℓ Dh encPt encT decT s .v0)
      (.eqN (opStEpoch P ℓ Dh encPt encT decT s 1 .v0) (.nat 0)))

def opWireOk {Γ : List (Ty S)} (c : Expr OO Γ (.base .ct)) : Expr OO Γ .bool :=
  isSomeE (opParseSenderKey P ℓ Dh encPt encT decT s c)

def opSenderKeyPt {Γ : List (Ty S)} (c : Expr OO Γ (.base .ct)) :
    Expr OO Γ (.opt (.base .key)) :=
  .caseOpt (opParseSenderKey P ℓ Dh encPt encT decT s c)
    .none
    (.caseOpt (opDecT P ℓ Dh encPt encT decT s .v0)
      .none
      (.ite
        (orE (opIsZeroPt P ℓ Dh encPt encT decT s .v0)
          (.not (opEqBytes P ℓ Dh encPt encT decT s
            (opEncT P ℓ Dh encPt encT decT s .v0) .v1)))
        .none
        (.some .v0)))

def opDhTargetPt {Γ : List (Ty S)} (g : Expr OO Γ (.base .st))
    (c : Expr OO Γ (.base .ct)) : Expr OO Γ (.opt (.base .key)) :=
  .letE (.pair g c)
    (.caseOpt (opSenderKeyPt P ℓ Dh encPt encT decT s (.snd .v0))
      .none
      (.ite (opHasSenderChain P ℓ Dh encPt encT decT s (.fst .v1))
        (.some .v0)
        .none))

def opNeedsDH {Γ : List (Ty S)} (g : Expr OO Γ (.base .st))
    (c : Expr OO Γ (.base .ct)) : Expr OO Γ .bool :=
  .letE (.pair g c)
    (.caseOpt (opParseSenderKey P ℓ Dh encPt encT decT s (.snd .v0))
      (.bool false)
      (.not (opHasRecvChain P ℓ Dh encPt encT decT s (.fst .v1) .v0)))

def opSendHalfReal {Γ : List (Ty S)} (rkM : Expr OO Γ (.base .rcoins))
    (c : Expr OO Γ (.base .ct)) (rc : Expr OO Γ (.base .rcoins)) :
    Expr OO Γ (.opt (.prod (.base .rcoins) (.base .rcoins))) :=
  .letE (.pair rkM (.pair c rc))
    (.caseOpt (opParseSenderKey P ℓ Dh encPt encT decT s (.fst (.snd .v0)))
      .none
      (opRootCreateChain P ℓ Dh encPt encT decT s
        (.fst .v1) .v0 (.snd (.snd .v1))))

def opBadAt {Γ : List (Ty S)} (s' : Expr OO Γ (.base .rcoins))
    (g : Expr OO Γ (.base .st)) (c : Expr OO Γ (.base .ct)) : Expr OO Γ .bool :=
  .letE (.pair s' (.pair g c))
    (.and
      (.and (.not (opStParty P ℓ Dh encPt encT decT s (.fst (.snd .v0))))
        (opHasEpoch0Chain P ℓ Dh encPt encT decT s (.fst (.snd .v0))))
      (.caseOpt (opParseSenderKey P ℓ Dh encPt encT decT s (.snd (.snd .v0)))
        (.bool false)
        (opEqBytes P ℓ Dh encPt encT decT s .v0
          (opGenPub P ℓ Dh encPt encT decT s (.fst .v1)))))

def opFinishHop2DH {Γ : List (Ty S)} (g : Expr OO Γ (.base .st))
    (c : Expr OO Γ (.base .ct)) (rc rk2 ckR ckS : Expr OO Γ (.base .rcoins)) :
    Expr OO Γ (.opt (.prod (.base .st) (.prod .nat (.prod .nat (.base .msg))))) :=
  .letE (.pair g (.pair c (.pair rc (.pair rk2 (.pair ckR ckS)))))
    (.caseOpt (opParseSenderKey P ℓ Dh encPt encT decT s (.fst (.snd .v0)))
      .none
      (.ite (opHasSenderChain P ℓ Dh encPt encT decT s (.fst .v1))
        (let g1 : Expr OO _ (.base .st) := .fst .v1
         let c1 : Expr OO _ (.base .ct) := .fst (.snd .v1)
         let rc1 : Expr OO _ (.base .rcoins) := .fst (.snd (.snd .v1))
         let rk2_1 : Expr OO _ (.base .rcoins) := .fst (.snd (.snd (.snd .v1)))
         let ckR_1 : Expr OO _ (.base .rcoins) := .fst (.snd (.snd (.snd (.snd .v1))))
         let ckS_1 : Expr OO _ (.base .rcoins) := .snd (.snd (.snd (.snd (.snd .v1))))
         let st1 := opAdvancePrevCounter P ℓ Dh encPt encT decT s g1
         let st2 := opPushRecvChain P ℓ Dh encPt encT decT s st1 .v0 ckR_1
         let st3 := opSetSenderChain P ℓ Dh encPt encT decT s st2 rc1 ckS_1
         let st4 := opSetRootKey P ℓ Dh encPt encT decT s st3 rk2_1
         opTryDecryptWhisper P ℓ Dh encPt encT decT s B st4 c1 rc1)
        .none))

def opFinishRecvB0 {Γ : List (Ty S)} (g : Expr OO Γ (.base .st))
    (c : Expr OO Γ (.base .ct)) (rc prk : Expr OO Γ (.base .rcoins)) :
    Expr OO Γ (.opt (.prod (.base .st) (.prod .nat (.prod .nat (.base .msg))))) :=
  .letE (.pair g (.pair c (.pair rc (opRootExpand P ℓ Dh encPt encT decT s prk))))
    (.caseOpt (opParseSenderKey P ℓ Dh encPt encT decT s (.fst (.snd .v0)))
      .none
      (.caseOpt
        (opRootCreateChain P ℓ Dh encPt encT decT s
          (.fst (.snd (.snd (.snd .v1)))) .v0 (.fst (.snd (.snd .v1))))
        .none
        (let g2 : Expr OO _ (.base .st) := .fst .v2
         let c2 : Expr OO _ (.base .ct) := .fst (.snd .v2)
         let rc2 : Expr OO _ (.base .rcoins) := .fst (.snd (.snd .v2))
         let ck1 : Expr OO _ (.base .rcoins) := .snd (.snd (.snd (.snd .v2)))
         let pkBytes : Expr OO _ (.base .ct) := .v1
         let rk2 : Expr OO _ (.base .rcoins) := .fst .v0
         let ck2 : Expr OO _ (.base .rcoins) := .snd .v0
         let st1 := opResetEpoch0 P ℓ Dh encPt encT decT s g2
         let st2 := opPushRecvChain P ℓ Dh encPt encT decT s st1 pkBytes ck1
         let st3 := opSetSenderChain P ℓ Dh encPt encT decT s st2 rc2 ck2
         let st4 := opSetRootKey P ℓ Dh encPt encT decT s st3 rk2
         opTryDecryptWhisper P ℓ Dh encPt encT decT s B st4 c2 rc2)))

@[simp] theorem opInitA_eval {Γ : List (Ty S)}
    (rk1 ck0 spkSc alice pqr ck1 : Expr OO Γ (.base .rcoins)) (ρ : Env Γ) :
    (opInitA P ℓ Dh encPt encT decT s rk1 ck0 spkSc alice pqr ck1).eval ρ =
      e2eInitA P (rk1.eval ρ, ck0.eval ρ, spkSc.eval ρ, alice.eval ρ, pqr.eval ρ, ck1.eval ρ) := by
  simp [opInitA, e2eInitA, Expr.eval]

@[simp] theorem opInitA_cost {Γ : List (Ty S)}
    (rk1 ck0 spkSc alice pqr ck1 : Expr OO Γ (.base .rcoins)) :
    (opInitA P ℓ Dh encPt encT decT s rk1 ck0 spkSc alice pqr ck1).cost =
      rk1.cost + pqr.cost + spkSc.cost + ck0.cost + alice.cost + ck1.cost + 12 := by
  simp only [opInitA, opSetPendingPreKey_cost, opSetSenderChain_cost, opAddRecvChain_cost,
    opNewSession_cost, opGenPub_cost, Expr.cost]
  omega

@[simp] theorem opInitB_eval {Γ : List (Ty S)}
    (rk ck0 spkSc alice pqr : Expr OO Γ (.base .rcoins)) (ρ : Env Γ) :
    (opInitB P ℓ Dh encPt encT decT s rk ck0 spkSc alice pqr).eval ρ =
      e2eInitB P (rk.eval ρ, ck0.eval ρ, spkSc.eval ρ, alice.eval ρ, pqr.eval ρ) := rfl

@[simp] theorem opInitB_cost {Γ : List (Ty S)}
    (rk ck0 spkSc alice pqr : Expr OO Γ (.base .rcoins)) :
    (opInitB P ℓ Dh encPt encT decT s rk ck0 spkSc alice pqr).cost =
      rk.cost + pqr.cost + spkSc.cost + ck0.cost + 7 := by
  simp only [opInitB, opSetSenderChain_cost, opNewSession_cost, Expr.cost]
  omega

@[simp] theorem opIsB0_eval {Γ : List (Ty S)} (g : Expr OO Γ (.base .st)) (ρ : Env Γ) :
    (opIsB0 P ℓ Dh encPt encT decT s g).eval ρ =
      ((g.eval ρ).party == .B && (g.eval ρ).epoch == 0) := by
  simp only [opIsB0, opStParty_eval, opStEpoch_eval,
    Expr.eval, Expr.v0, Env.get_cons_zero]
  have h : ∀ (p : Party) (e : ℕ),
      (partyEnc p && decide (min e 1 = 0)) = (p == .B && e == 0) := by
    rintro (_ | _) (_ | _ | e) <;> rfl
  exact h _ _

@[simp] theorem opIsB0_cost {Γ : List (Ty S)} (g : Expr OO Γ (.base .st)) :
    (opIsB0 P ℓ Dh encPt encT decT s g).cost = g.cost + 8 := by
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  simp only [opIsB0, opStParty_cost, opStEpoch_cost, Expr.cost, Expr.v0, hb0, hb1]

@[simp] theorem opWireOk_eval {Γ : List (Ty S)} (c : Expr OO Γ (.base .ct)) (ρ : Env Γ) :
    (opWireOk P ℓ Dh encPt encT decT s c).eval ρ =
      (SignalMessage.tryFrom P.codec (c.eval ρ)).isOk := by
  simp only [opWireOk, isSomeE_eval, opParseSenderKey_eval]
  rcases SignalMessage.tryFrom P.codec (c.eval ρ) with _ | msg <;> rfl

@[simp] theorem opWireOk_cost {Γ : List (Ty S)} (c : Expr OO Γ (.base .ct)) :
    (opWireOk P ℓ Dh encPt encT decT s c).cost = c.cost + 3 := by
  simp only [opWireOk, isSomeE, opParseSenderKey_cost, Expr.cost]
  omega

@[simp] theorem opSenderKeyPt_eval {Γ : List (Ty S)} (c : Expr OO Γ (.base .ct)) (ρ : Env Γ) :
    (opSenderKeyPt P ℓ Dh encPt encT decT s c).eval ρ =
      senderKeyPt P encT decT (c.eval ρ) := by
  simp only [opSenderKeyPt, opParseSenderKey_eval, opDecT_eval, opIsZeroPt_eval,
    opEqBytes_eval, opEncT_eval, senderKeyPt, orE_eval,
    Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ]
  rcases SignalMessage.tryFrom P.codec (c.eval ρ) with _ | msg
  · rfl
  · simp only [bytesToPk?_pkToBytes, Option.bind_some]
    rcases decT msg.senderRatchetKey with _ | T
    · rfl
    · by_cases h0 : T = 0
      · simp [h0]
      · by_cases heq : encT T = msg.senderRatchetKey
        · simp [h0, heq]
        · simp [h0, heq]; exact mt (pkToBytes_inj _ _).mp heq

@[simp] theorem opSenderKeyPt_cost {Γ : List (Ty S)} (c : Expr OO Γ (.base .ct)) :
    (opSenderKeyPt P ℓ Dh encPt encT decT s c).cost = c.cost + 17 := by
  simp only [opSenderKeyPt, opParseSenderKey_cost, opDecT_cost, opIsZeroPt_cost,
    opEqBytes_cost, opEncT_cost, orE, Expr.cost, Expr.v0, Expr.v1]
  omega

@[simp] theorem opDhTargetPt_eval {Γ : List (Ty S)} (g : Expr OO Γ (.base .st))
    (c : Expr OO Γ (.base .ct)) (ρ : Env Γ) :
    (opDhTargetPt P ℓ Dh encPt encT decT s g c).eval ρ =
      dhTargetPt P encT decT (g.eval ρ) (c.eval ρ) := by
  simp only [opDhTargetPt, Expr.eval, opSenderKeyPt_eval, opHasSenderChain_eval,
    Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ,
    senderKeyPt, dhTargetPt]
  rcases SignalMessage.tryFrom P.codec (c.eval ρ) with _ | msg
  · rfl
  · dsimp only
    rcases decT msg.senderRatchetKey with _ | T
    · rfl
    · dsimp only
      by_cases hbad : T = 0 ∨ encT T ≠ msg.senderRatchetKey
      · simp [hbad]
      · simp only [hbad, ↓reduceIte]
        have hsc : ∀ (o : Option SenderChain),
            (if o.isSome = true then some T else none) =
              (match o with | none => none | some _ => some T) := fun o => by cases o <;> rfl
        exact hsc _

@[simp] theorem opDhTargetPt_cost {Γ : List (Ty S)} (g : Expr OO Γ (.base .st))
    (c : Expr OO Γ (.base .ct)) :
    (opDhTargetPt P ℓ Dh encPt encT decT s g c).cost = g.cost + c.cost + 28 := by
  simp only [opDhTargetPt, opSenderKeyPt_cost, opHasSenderChain_cost,
    Expr.cost, Expr.v0, Expr.v1]
  omega

@[simp] theorem opNeedsDH_eval {Γ : List (Ty S)} (g : Expr OO Γ (.base .st))
    (c : Expr OO Γ (.base .ct)) (ρ : Env Γ) :
    (opNeedsDH P ℓ Dh encPt encT decT s g c).eval ρ =
      needsDH P (g.eval ρ) (c.eval ρ) := by
  simp only [opNeedsDH, opParseSenderKey_eval, opHasRecvChain_eval, needsDH,
    Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ]
  rcases SignalMessage.tryFrom P.codec (c.eval ρ) with _ | msg
  · rfl
  · simp only [bytesToPk?_pkToBytes]
    have hnot : ∀ (o : Option ℕ), (!o.isSome) = o.isNone := fun o => by cases o <;> rfl
    exact hnot _

@[simp] theorem opNeedsDH_cost {Γ : List (Ty S)} (g : Expr OO Γ (.base .st))
    (c : Expr OO Γ (.base .ct)) :
    (opNeedsDH P ℓ Dh encPt encT decT s g c).cost = g.cost + c.cost + 12 := by
  simp only [opNeedsDH, opParseSenderKey_cost, opHasRecvChain_cost,
    Expr.cost, Expr.v0, Expr.v1]
  omega

@[simp] theorem opSendHalfReal_eval {Γ : List (Ty S)} (rkM : Expr OO Γ (.base .rcoins))
    (c : Expr OO Γ (.base .ct)) (rc : Expr OO Γ (.base .rcoins)) (ρ : Env Γ) :
    (opSendHalfReal P ℓ Dh encPt encT decT s rkM c rc).eval ρ =
      sendHalfReal P (rkM.eval ρ) (c.eval ρ) (rc.eval ρ) := by
  simp only [opSendHalfReal, opParseSenderKey_eval, opRootCreateChain_eval, sendHalfReal,
    Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ]
  rcases SignalMessage.tryFrom P.codec (c.eval ρ) with _ | msg
  · rfl
  · simp only [bytesToPk?_pkToBytes]

@[simp] theorem opSendHalfReal_cost {Γ : List (Ty S)} (rkM : Expr OO Γ (.base .rcoins))
    (c : Expr OO Γ (.base .ct)) (rc : Expr OO Γ (.base .rcoins)) :
    (opSendHalfReal P ℓ Dh encPt encT decT s rkM c rc).cost =
      rkM.cost + c.cost + rc.cost + 17 := by
  simp only [opSendHalfReal, opParseSenderKey_cost, opRootCreateChain_cost,
    Expr.cost, Expr.v0, Expr.v1]
  omega

@[simp] theorem opBadAt_eval {Γ : List (Ty S)} (s' : Expr OO Γ (.base .rcoins))
    (g : Expr OO Γ (.base .st)) (c : Expr OO Γ (.base .ct)) (ρ : Env Γ) :
    (opBadAt P ℓ Dh encPt encT decT s s' g c).eval ρ =
      hop2BadAt P (s'.eval ρ) (g.eval ρ) (c.eval ρ) := by
  simp only [opBadAt, opStParty_eval, opHasEpoch0Chain_eval, opParseSenderKey_eval,
    opEqBytes_eval, opGenPub_eval, hop2BadAt, Expr.eval, Expr.v0, Expr.v1,
    Env.get_cons_zero, Env.get_cons_succ]
  have hp : (!(partyEnc (g.eval ρ).party)) = ((g.eval ρ).party == .A) := by
    cases (g.eval ρ).party <;> rfl
  rw [hp]
  rcases SignalMessage.tryFrom P.codec (c.eval ρ) with _ | msg
  · rfl
  · exact congrArg _ (pkToBytes_beq _ _)

@[simp] theorem opBadAt_cost {Γ : List (Ty S)} (s' : Expr OO Γ (.base .rcoins))
    (g : Expr OO Γ (.base .st)) (c : Expr OO Γ (.base .ct)) :
    (opBadAt P ℓ Dh encPt encT decT s s' g c).cost =
      s'.cost + g.cost + c.cost + 25 := by
  simp only [opBadAt, opStParty_cost, opHasEpoch0Chain_cost, opParseSenderKey_cost,
    opEqBytes_cost, opGenPub_cost, Expr.cost, Expr.v0, Expr.v1]
  omega

@[simp] theorem opFinishHop2DH_eval {Γ : List (Ty S)} (g : Expr OO Γ (.base .st))
    (c : Expr OO Γ (.base .ct)) (rc rk2 ckR ckS : Expr OO Γ (.base .rcoins)) (ρ : Env Γ) :
    (opFinishHop2DH P ℓ Dh encPt encT decT s B g c rc rk2 ckR ckS).eval ρ =
      (finishHop2DH P ℓ (g.eval ρ) (c.eval ρ) (rc.eval ρ)
        (rk2.eval ρ) (ckR.eval ρ) (ckS.eval ρ)).map
        (fun (st', t', i', m') => (st', min t' B, min i' B, m')) := by
  simp only [opFinishHop2DH, opParseSenderKey_eval, opHasSenderChain_eval,
    opAdvancePrevCounter_eval, opPushRecvChain_eval, opSetSenderChain_eval,
    opSetRootKey_eval, opTryDecryptWhisper_eval,
    Expr.eval, Expr.v0, Expr.v1, Env.get_cons_zero, Env.get_cons_succ]
  rcases htry : SignalMessage.tryFrom P.codec (c.eval ρ) with _ | msg
  · simp [finishHop2DH, htry]
  · simp only [bytesToPk?_pkToBytes, List.length_append, List.length_singleton,
      SessionState.setSenderChain]
    have h : ∀ (gv : GhostState Bytes),
        (if gv.session.senderChain.isSome = true then
          match SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs gv.party)
              msg .whisper (rc.eval ρ)
              { gv.session with
                rootKey := rk2.eval ρ
                previousCounter := match gv.session.senderChain with
                  | none => gv.session.previousCounter
                  | some sc => if sc.chainKey.index = 0 then 0 else sc.chainKey.index - 1
                senderChain :=
                  some ⟨KeyPair.generate P.C (rc.eval ρ), ⟨ckS.eval ρ, 0⟩⟩
                receiverChains := RatchetState.evictReceiverChains
                  (gv.session.receiverChains ++
                    [⟨msg.senderRatchetKey, some ⟨ckR.eval ρ, 0⟩, []⟩]) } with
          | (.error _, _) => none
          | (.ok m, s_out) =>
            some ({ gv with
              session := s_out
              epoch := gv.epoch + 1
              chainEpochs := (gv.chainEpochs ++ [gv.epoch + 1]).drop
                (gv.chainEpochs.length + 1 - s_out.receiverChains.length) },
              min (gv.epoch + 1) B, min (msg.counter.toNat + 1) B, padOrTruncatePlain ℓ m)
        else none) =
        (finishHop2DH P ℓ gv (c.eval ρ) (rc.eval ρ)
          (rk2.eval ρ) (ckR.eval ρ) (ckS.eval ρ)).map
          (fun (st', t', i', m') => (st', min t' B, min i' B, m')) := by
      intro gv
      unfold finishHop2DH
      rw [htry]
      dsimp only
      rcases gv.session.senderChain with _ | sc
      · rfl
      · simp only [Option.isSome_some, ↓reduceIte]
        rcases SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs gv.party)
            msg .whisper (rc.eval ρ) _ with ⟨_ | m, s_out⟩ <;> rfl
    exact h (g.eval ρ)

@[simp] theorem opFinishHop2DH_cost {Γ : List (Ty S)} (g : Expr OO Γ (.base .st))
    (c : Expr OO Γ (.base .ct)) (rc rk2 ckR ckS : Expr OO Γ (.base .rcoins)) :
    (opFinishHop2DH P ℓ Dh encPt encT decT s B g c rc rk2 ckR ckS).cost =
      g.cost + c.cost + rc.cost + rk2.cost + ckR.cost + ckS.cost + bits B + 57 := by
  simp only [opFinishHop2DH, opParseSenderKey_cost, opHasSenderChain_cost,
    opAdvancePrevCounter_cost, opPushRecvChain_cost, opSetSenderChain_cost,
    opSetRootKey_cost, opTryDecryptWhisper_cost, Expr.cost, Expr.v0, Expr.v1]
  omega

@[simp] theorem opFinishRecvB0_eval {Γ : List (Ty S)} (g : Expr OO Γ (.base .st))
    (c : Expr OO Γ (.base .ct)) (rc prk : Expr OO Γ (.base .rcoins)) (ρ : Env Γ) :
    (opFinishRecvB0 P ℓ Dh encPt encT decT s B g c rc prk).eval ρ =
      (finishRecvB0 P ℓ (g.eval ρ) (c.eval ρ) (rc.eval ρ) (prk.eval ρ)).map
        (fun (st', t', i', m') => (st', min t' B, min i' B, m')) := by
  simp only [opFinishRecvB0, opRootExpand_eval, opParseSenderKey_eval, opRootCreateChain_eval,
    opResetEpoch0_eval, opPushRecvChain_eval, opSetSenderChain_eval, opSetRootKey_eval,
    opTryDecryptWhisper_eval, finishRecvB0, Expr.eval, Expr.v0, Expr.v1, Expr.v2,
    Env.get_cons_zero, Env.get_cons_succ]
  rcases htry : SignalMessage.tryFrom P.codec (c.eval ρ) with _ | msg
  · rfl
  · simp only [bytesToPk?_pkToBytes]
    rcases hrc : rootCreateChain P.C ((expandPRG P.C.F).gen (prk.eval ρ)).1 msg.senderRatchetKey
        (KeyPair.generate P.C (rc.eval ρ)).privateKey with _ | ⟨rk2, ck2⟩
    · rfl
    · simp only [List.nil_append, Nat.zero_add, evictReceiverChains_singleton,
        List.length_singleton, SessionState.setSenderChain,
        rootCreateChain_index_zero P.C _ _ _ _ _ hrc]
      rcases SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs (g.eval ρ).party)
          msg .whisper (rc.eval ρ) _ with ⟨_ | m, s_out⟩ <;> rfl

@[simp] theorem opFinishRecvB0_cost {Γ : List (Ty S)} (g : Expr OO Γ (.base .st))
    (c : Expr OO Γ (.base .ct)) (rc prk : Expr OO Γ (.base .rcoins)) :
    (opFinishRecvB0 P ℓ Dh encPt encT decT s B g c rc prk).cost =
      g.cost + c.cost + rc.cost + prk.cost + bits B + 58 := by
  simp only [opFinishRecvB0, opRootExpand_cost, opParseSenderKey_cost, opRootCreateChain_cost,
    opResetEpoch0_cost, opPushRecvChain_cost, opSetSenderChain_cost, opSetRootKey_cost,
    opTryDecryptWhisper_cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2]
  omega

variable [SampleableType PQC]

def spkDrawBool {Γ : List (Ty S)} : Comp OO II Γ .bool :=
  rdsl do sample (I := II) (Sum.inr .bool) ()

def spkDrawBv {Γ : List (Ty S)} : Comp OO II Γ (.base .rcoins) :=
  rdsl do sample (I := II) (Sum.inr (.base true)) ()

def spkDrawCoins
    {O' : Ops S} {Γ : List (Ty S)} : Comp O' II Γ (.opt (.base .coins)) :=
  rdsl do
    r ← sample (I := II) (Sum.inr (.base false)) ()
    return some r

def initAOracleC {Γ : List (Ty S)}
    (ck0 sE alice pqr : Expr OO Γ (.base .rcoins)) : Comp OO II Γ (.base .st) :=
  rdsl do
    (ck0_0, s0, alice0, pqr0) ← return (ck0, sE, alice, pqr)
    let pt := opDh P ℓ Dh encPt encT decT s s0
      (opDh P ℓ Dh encPt encT decT s alice0 (opBasePt P ℓ Dh encPt encT decT s))
    prk ← query (I := II) () pt
    let rkck := opRootExpand P ℓ Dh encPt encT decT s prk
    return opInitA P ℓ Dh encPt encT decT s rkck.1 ck0_0 s0 alice0 pqr0 rkck.2

def receiveB0C {Γ : List (Ty S)}
    (sE : Expr OO Γ (.base .rcoins)) (g : Expr OO Γ (.base .st))
    (c : Expr OO Γ (.base .ct)) (rc : Expr OO Γ (.base .rcoins)) :
    Comp OO II Γ (.opt (.prod (.base .st) (.prod .nat (.prod .nat (.base .msg))))) :=
  rdsl do
    (s0, g0, c0, rc0) ← return (sE, g, c, rc)
    match opSenderKeyPt P ℓ Dh encPt encT decT s c0 with
    | none => return none
    | some ptT =>
      prk ← query (I := II) () (opDh P ℓ Dh encPt encT decT s s0 ptT)
      return opFinishRecvB0 P ℓ Dh encPt encT decT s B g0 c0 rc0 prk

def receiveSpkC {Γ : List (Ty S)}
    (sE : Expr OO Γ (.base .rcoins)) (g : Expr OO Γ (.base .st))
    (c : Expr OO Γ (.base .ct)) (rc : Expr OO Γ (.base .rcoins)) :
    Comp OO II Γ (.opt (.prod (.base .st) (.prod .nat (.prod .nat (.base .msg))))) :=
  rdsl do
    (s0, g0, c0, rc0) ← return (sE, g, c, rc)
    if opIsB0 P ℓ Dh encPt encT decT s g0 then
      receiveB0C P ℓ Dh encPt encT decT s B s0 g0 c0 rc0
    else
      return opReceive P ℓ Dh encPt encT decT s B g0 c0 rc0

def deliverSpkC {Γ : List (Ty S)}
    (stE : Expr OO Γ GS) (arg : Expr OO Γ (.prod .bool (.base .ct))) :
    Comp OO II Γ (.prod (.opt RR) GS) :=
  rdsl do
    (gs0, p0, c0) ← return (stE, arg)
    let inTr := ((inTransitE K gs0 (otherE p0) c0 : Expr OSM _ (.opt recTy)).liftL)
    if gsWin gs0 then
      return (none, gs0)
    else
      match inTr with
      | none => return (none, gs0)
      | some rec0 =>
        rc ← spkDrawBv P ℓ Dh encPt encT decT s
        resOpt ← receiveSpkC P ℓ Dh encPt encT decT s B
          (opSpkSc P ℓ Dh encPt encT decT s) (pGet (gsSt gs0) p0) c0 rc
        match resOpt with
        | none => return (some (.inl ()), gs0)
        | some (st', t', i', m') =>
          let rPos := recPos rec0
          let s1 := acceptE K gs0 p0 st' rPos
          let mOut := if challContainsE K gs0 rPos then none else some m'
          return (some (.inr (t', i', mOut)), s1)

def injectSpkC {Γ : List (Ty S)}
    (stE : Expr OO Γ GS) (arg : Expr OO Γ (.prod .bool (.base .ct))) :
    Comp OO II Γ (.prod (.opt RR) GS) :=
  rdsl do
    (gs0, p0, c0) ← return (stE, arg)
    let inTr := ((inTransitE K gs0 (otherE p0) c0 : Expr OSM _ (.opt recTy)).liftL)
    let refuse :=
      orE (gsWin gs0)
        (orE (isSomeE inTr)
          (orE (!(safeInjE (raw 3) gs0))
            (!(opInjOK P ℓ Dh encPt encT decT s c0))))
    if refuse then
      return (none, gs0)
    else
      rc ← spkDrawBv P ℓ Dh encPt encT decT s
      resOpt ← receiveSpkC P ℓ Dh encPt encT decT s B
        (opSpkSc P ℓ Dh encPt encT decT s) (pGet (gsSt gs0) p0) c0 rc
      match resOpt with
      | none => return (some (.inl ()), gs0)
      | some (st', t', i', m') =>
        if nat (qep + 1) < t' then
          return (some (.inl ()), gs0)
        else
          let pos := (otherE p0, t', i')
          if trivialE K (raw 3) gs0 pos then
            return (some (.inr (t', i', some m')), acceptE K gs0 p0 st' pos)
          else
            return (some (.inl ()), gsSetWin gs0 true)

def spkOracleImplC {Γ : List (Ty S)}
    (stE : Expr OO Γ GS)
    (q : Expr OO Γ (smQ Pt (GhostState Bytes) Unit (CBC.Plain ℓ) PQC (BitVec 256) Bytes)) :
    Comp OO II Γ
      (.prod (smR Pt (GhostState Bytes) Unit (CBC.Plain ℓ) PQC (BitVec 256) Bytes .st) GS) :=
  rdsl do
    (gs0, qry) ← return (stE, q)
    match qry with
    | .transmit qTr =>
      res ← ((transmitRC (I := II) 3 qep (ConfigRC.spkS OSM)
        (spkDrawCoins ℓ (PQC := PQC)) gs0 qTr).liftL)
      return (.inl (.inl (.inl (.inl res.1))), res.2)
    | .challenge qCh =>
      res ← ((challRC (I := II) 3 qep (ConfigRC.spkS OSM)
        (spkDrawCoins ℓ (PQC := PQC)) gs0 qCh).liftL)
      return (.inl (.inl (.inl (.inr res.1))), res.2)
    | .deliver qDl =>
      res ← deliverSpkC P ℓ Dh encPt encT decT s K B gs0 qDl
      return (.inl (.inl (.inr res.1)), res.2)
    | .inject qIj =>
      res ← injectSpkC P ℓ Dh encPt encT decT s K B qep gs0 qIj
      return (.inl (.inr res.1), res.2)
    | .corrupt pCorr =>
      res ← ((corrRC (I := II) K (ConfigRC.spkS OSM) gs0 pCorr).liftL)
      return (.inr res.1, res.2)

/-- Costed `spkLeakRed` PRF reduction. -/
def spkLeakRedProg :
    CostedReduction (spkLeakSessionOps P ℓ Dh encPt encT decT s) (e2ePrfIface Pt ℓ PQC)
      (SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) (e2eCodec Pt ℓ PQC)
      .unit .unit .bool .bool where
  σ := GS
  init :=
    rdsl [_] do
      b ← spkDrawBool P ℓ Dh encPt encT decT s
      ck0 ← spkDrawBv P ℓ Dh encPt encT decT s
      alice ← spkDrawBv P ℓ Dh encPt encT decT s
      pqr ← spkDrawBv P ℓ Dh encPt encT decT s
      let sE := opSpkSc P ℓ Dh encPt encT decT s
      stA ← initAOracleC P ℓ Dh encPt encT decT s ck0 sE alice pqr
      let zeroBv := opZeroBv P ℓ Dh encPt encT decT s
      let stB := opInitB P ℓ Dh encPt encT decT s zeroBv ck0 sE alice pqr
      let initGs :=
        gsMk (stA, stB) b false
          (0, 0) (0, 0)
          none [] [] []
          (tconst 0, tconst 0)
          [] []
      return ((), initGs)
  handle := rdsl [gs0, qry] do spkOracleImplC P ℓ Dh encPt encT decT s K B qep gs0 qry
  finish := rdsl [gs0, b'] do return orE (boolEq (gsB gs0) b') (gsWin gs0)

end SpkLeakRedProg

/-! ## Query-budget invariant `SMBudgetInv` -/

section SMBudgetInv

variable {St Msg C : Type}

/-- Query-budget invariant bounding `SM.GameState` list lengths in terms of remaining queries `q` out of `qAdv`. -/
structure SMBudgetInv (qAdv K : ℕ) (q : ℕ) (s : SM.GameState St Msg C) : Prop where
  trans_le : s.trans.length + q ≤ qAdv
  chall_le : s.chall.length + q ≤ qAdv
  leaks_le : s.leaks.length + q ≤ qAdv
  corrs_le : s.corrs.length + q ≤ qAdv
  comp_u : ∃ U : List SM.Pos, U.length + q ≤ qAdv ∧ CountLe s.comp U ∧ ∀ r ∈ s.trans, r.pos ∈ U
  qAdv_sq_le : qAdv * qAdv ≤ K * K

theorem nat_le_mul_self (n : ℕ) : n ≤ n * n := by
  rcases n with _ | m
  · omega
  · exact Nat.le_mul_of_pos_right (m + 1) (Nat.succ_pos m)

theorem SMBudgetInv.qAdv_le {qAdv K q : ℕ} {s : SM.GameState St Msg C}
    (h : SMBudgetInv qAdv K q s) : qAdv ≤ K := by
  have := h.qAdv_sq_le
  nlinarith

theorem SMBudgetInv.toBounded {qAdv K q : ℕ} {s : SM.GameState St Msg C}
    (h : SMBudgetInv qAdv K q s) : SMStateBounded K s := by
  have hK := h.qAdv_le
  have h1 := h.trans_le
  have h2 := h.chall_le
  have h3 := h.leaks_le
  have h4 := h.corrs_le
  rcases h.comp_u with ⟨U, hUlen, hCU, htrU⟩
  exact ⟨by omega, by omega, ⟨U, by omega, hCU, htrU⟩, by omega, by omega⟩

theorem SMBudgetInv.mono {qAdv K m n : ℕ} {s : SM.GameState St Msg C}
    (hmn : m ≤ n) (h : SMBudgetInv qAdv K n s) : SMBudgetInv qAdv K m s := by
  have h1 := h.trans_le
  have h2 := h.chall_le
  have h3 := h.leaks_le
  have h4 := h.corrs_le
  rcases h.comp_u with ⟨U, hUlen, hCU, htrU⟩
  exact ⟨by omega, by omega, by omega, by omega, ⟨U, by omega, hCU, htrU⟩, h.qAdv_sq_le⟩

theorem SMBudgetInv.init {qAdv K : ℕ} (hK : qAdv * qAdv ≤ K * K)
    (st : Party → St) (b : Bool) :
    SMBudgetInv qAdv K qAdv ({ st := st, b := b } : SM.GameState St Msg C) :=
  ⟨by simp, by simp, by simp, by simp,
    ⟨[], by simp, countLe_nil [], fun _ h => nomatch h⟩, hK⟩

theorem epMgmt_lengths {Δ qep : ℕ} {P : Party} {bad : Bool}
    {s s₁ : SM.GameState St Msg C} (h : s.epMgmt Δ qep P bad = some s₁) :
    s₁.trans.length = s.trans.length ∧
    s₁.chall.length = s.chall.length ∧
    s₁.comp.length = s.comp.length ∧
    s₁.leaks.length ≤ s.leaks.length + 1 ∧
    s₁.corrs.length = s.corrs.length := by
  unfold GameState.epMgmt at h
  by_cases hsends : P.sendsIn (s.epoch P + 1)
  · simp only [hsends, ↓reduceIte] at h
    by_cases hqep : qep < s.epoch P + 1
    · simp [hqep] at h
    · simp only [hqep, ↓reduceIte, Option.some.injEq] at h
      subst h
      by_cases hbad : (bad && !s.safeCh Δ P) <;> simp [hbad, GameState.leak]
  · simp only [hsends, Bool.false_eq_true, ↓reduceIte] at h
    by_cases hqep : qep < s.epoch P
    · simp [hqep] at h
    · simp only [hqep, ↓reduceIte, Option.some.injEq] at h
      subst h; exact ⟨rfl, rfl, rfl, Nat.le_succ _, rfl⟩

theorem epMgmt_trans_comp {Δ qep : ℕ} {P : Party} {bad : Bool}
    {s s₁ : SM.GameState St Msg C} (h : s.epMgmt Δ qep P bad = some s₁) :
    s₁.trans = s.trans ∧ s₁.comp = s.comp := by
  unfold GameState.epMgmt at h
  by_cases hsends : P.sendsIn (s.epoch P + 1)
  · simp only [hsends, ↓reduceIte] at h
    by_cases hqep : qep < s.epoch P + 1
    · simp [hqep] at h
    · simp only [hqep, ↓reduceIte, Option.some.injEq] at h
      subst h
      by_cases hbad : (bad && !s.safeCh Δ P) <;> simp [hbad, GameState.leak]
  · simp only [hsends, Bool.false_eq_true, ↓reduceIte] at h
    by_cases hqep : qep < s.epoch P
    · simp [hqep] at h
    · simp only [hqep, ↓reduceIte, Option.some.injEq] at h
      subst h; exact ⟨rfl, rfl⟩

theorem epMgmt_b {Δ qep : ℕ} {P : Party} {bad : Bool}
    {s s₁ : SM.GameState St Msg C} (h : s.epMgmt Δ qep P bad = some s₁) :
    s₁.b = s.b := by
  unfold GameState.epMgmt at h
  by_cases hsends : P.sendsIn (s.epoch P + 1)
  · simp only [hsends, ↓reduceIte] at h
    by_cases hqep : qep < s.epoch P + 1
    · simp [hqep] at h
    · simp only [hqep, ↓reduceIte, Option.some.injEq] at h
      subst h
      by_cases hbad : (bad && !s.safeCh Δ P) <;> simp [hbad, GameState.leak]
  · simp only [hsends, Bool.false_eq_true, ↓reduceIte] at h
    by_cases hqep : qep < s.epoch P
    · simp [hqep] at h
    · simp only [hqep, ↓reduceIte, Option.some.injEq] at h
      subst h; rfl

theorem SMBudgetInv.epMgmt_record {qAdv K m Δ qep : ℕ} {P : Party} {bad isChall : Bool}
    {st' : St} {r : SM.Record Msg C} {s s₁ : SM.GameState St Msg C}
    (h : SMBudgetInv qAdv K (m + 1) s) (hep : s.epMgmt Δ qep P bad = some s₁) :
    SMBudgetInv qAdv K m (s₁.record Δ P st' r isChall) := by
  obtain ⟨htr, hch, _, hlk, hcr⟩ := epMgmt_lengths hep
  obtain ⟨htrEq, hcpEq⟩ := epMgmt_trans_comp hep
  have h1 := h.trans_le
  have h2 := h.chall_le
  have h3 := h.leaks_le
  have h4 := h.corrs_le
  rcases h.comp_u with ⟨U, hUlen, hCU, htrU⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, h.qAdv_sq_le⟩
  · simp only [GameState.record, List.length_cons, htr]; omega
  · simp only [GameState.record]; split_ifs <;> simp [hch] <;> omega
  · simp only [GameState.record]; omega
  · simp only [GameState.record, hcr]; omega
  · refine ⟨r.pos :: U, by simp only [List.length_cons]; omega, ?_, ?_⟩
    · simp only [GameState.record, hcpEq]
      split_ifs
      · exact countLe_cons_right r.pos hCU
      · exact countLe_cons_cons r.pos hCU
    · intro r' hr'
      simp only [GameState.record, htrEq, List.mem_cons] at hr'
      rcases hr' with rfl | hr'
      · simp
      · exact List.mem_cons_of_mem _ (htrU r' hr')

theorem SMBudgetInv.accept [DecidableEq C] {qAdv K m : ℕ} {P : Party} {st' : St} {pos : SM.Pos}
    {s : SM.GameState St Msg C} (h : SMBudgetInv qAdv K (m + 1) s) :
    SMBudgetInv qAdv K m (s.accept P st' pos) := by
  have hm := h.mono (Nat.le_succ m)
  have htr : (s.accept P st' pos).trans.length ≤ s.trans.length :=
    List.length_filter_le _ _
  have hch : (s.accept P st' pos).chall.length ≤ s.chall.length :=
    List.length_filter_le _ _
  have h1 := hm.trans_le
  have h2 := hm.chall_le
  have h3 := hm.leaks_le
  have h4 := hm.corrs_le
  rcases hm.comp_u with ⟨U, hUlen, hCU, htrU⟩
  refine ⟨by omega, by omega, h3, h4, ⟨U, hUlen, ?_, ?_⟩, h.qAdv_sq_le⟩
  · exact countLe_filter_left (· != pos) hCU
  · intro r hr
    exact htrU r (List.mem_of_mem_filter hr)

theorem SMBudgetInv.setWin {qAdv K m : ℕ} {s : SM.GameState St Msg C}
    (h : SMBudgetInv qAdv K (m + 1) s) :
    SMBudgetInv qAdv K m { s with win := true } := by
  have hm := h.mono (Nat.le_succ m)
  exact ⟨hm.trans_le, hm.chall_le, hm.leaks_le, hm.corrs_le, hm.comp_u, hm.qAdv_sq_le⟩

theorem SMBudgetInv.afterCorrDedup {qAdv K m : ℕ} {P : Party} {s : SM.GameState St Msg C}
    (h : SMBudgetInv qAdv K (m + 1) s) :
    SMBudgetInv qAdv K m (Computational.Proofs.GameHop.CompDedup.afterCorrDedup s P) := by
  have h1 := h.trans_le
  have h2 := h.chall_le
  have h3 := h.leaks_le
  have h4 := h.corrs_le
  rcases h.comp_u with ⟨U, hUlen, hCU, htrU⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, h.qAdv_sq_le⟩
  · simp only [Computational.Proofs.GameHop.CompDedup.afterCorrDedup, GameState.leak]; omega
  · simp only [Computational.Proofs.GameHop.CompDedup.afterCorrDedup, GameState.leak]; omega
  · simp only [Computational.Proofs.GameHop.CompDedup.afterCorrDedup, GameState.leak,
      List.length_cons]; omega
  · simp only [Computational.Proofs.GameHop.CompDedup.afterCorrDedup, GameState.leak,
      List.length_cons]; omega
  · refine ⟨U, by omega, ?_, htrU⟩
    dsimp only [Computational.Proofs.GameHop.CompDedup.afterCorrDedup, GameState.leak]
    refine countLe_dedupPrepend hCU ?_
    intro x hx
    rcases List.mem_map.mp hx with ⟨r, hr, rfl⟩
    exact htrU r (List.mem_of_mem_filter hr)

@[simp] theorem stateT_run_lift_bind {m : Type → Type} [Monad m] [LawfulMonad m]
    {σ α β : Type} (x : m α) (k : α → StateT σ m β) (s : σ) :
    (StateT.lift x >>= k).run s = (x >>= fun a => (k a).run s) := by
  simp [StateT.run_bind, StateT.run_lift]

@[simp] theorem stateT_run_monadLift_bind {m : Type → Type} [Monad m] [LawfulMonad m]
    {σ α β : Type} (x : m α) (k : α → StateT σ m β) (s : σ) :
    ((liftM x : StateT σ m α) >>= k).run s = (x >>= fun a => (k a).run s) := by
  simp [StateT.run_bind, StateT.run_monadLift, monadLift_self]

theorem SMBudgetInv.transmitR {Key Coins RCoins : Type} [SampleableType Coins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfgR : ConfigR St Msg C)
    (y : Party × Msg × Option Coins) {qAdv K m : ℕ} {s : SM.GameState St Msg C}
    (h : SMBudgetInv qAdv K (m + 1) s) :
    ∀ r ∈ support ((SM.transmitR sm Δ qep cfgR y).run s), SMBudgetInv qAdv K m r.2 := by
  rcases y with ⟨P, msg, optR⟩
  intro r hr
  unfold SM.transmitR SM.transmitImpl at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
  by_cases hok : !(cfgR.sendOK s P)
  · simp only [hok, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact h.mono (Nat.le_succ m)
  · simp only [hok, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      pure_bind] at hr
    by_cases hwin : s.win
    · simp only [hwin, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact h.mono (Nat.le_succ m)
    · simp only [hwin, Bool.false_eq_true, ↓reduceIte, stateT_run_monadLift_bind,
        mem_support_bind_iff] at hr
      obtain ⟨⟨coins, bad⟩, -, hr⟩ := hr
      rcases hep : s.epMgmt Δ qep P bad with _ | s₁
      · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact h.mono (Nat.le_succ m)
      · simp only [hep, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact h.epMgmt_record hep

theorem SMBudgetInv.challR {Key Coins RCoins : Type} [SampleableType Coins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfgR : ConfigR St Msg C)
    (y : Party × Msg × Msg × Option Coins) {qAdv K m : ℕ} {s : SM.GameState St Msg C}
    (h : SMBudgetInv qAdv K (m + 1) s) :
    ∀ r ∈ support ((SM.challR sm Δ qep cfgR y).run s), SMBudgetInv qAdv K m r.2 := by
  rcases y with ⟨P, m₀, m₁, optR⟩
  intro r hr
  unfold SM.challR SM.challImpl at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
  by_cases hok : !(cfgR.sendOK s P)
  · simp only [hok, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact h.mono (Nat.le_succ m)
  · simp only [hok, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      pure_bind] at hr
    by_cases hwin : s.win
    · simp only [hwin, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact h.mono (Nat.le_succ m)
    · simp only [hwin, Bool.false_eq_true, ↓reduceIte, stateT_run_monadLift_bind,
        mem_support_bind_iff] at hr
      obtain ⟨⟨coins, bad⟩, -, hr⟩ := hr
      rcases hep : s.epMgmt Δ qep P bad with _ | s₁
      · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact h.mono (Nat.le_succ m)
      · simp only [hep] at hr
        by_cases hch : (!s₁.safeCh Δ P || !cfgR.base.challAllowedIn (s₁.epoch P))
        · simp only [hch, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact h.mono (Nat.le_succ m)
        · simp only [hch, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
            StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact h.epMgmt_record hep

theorem SMBudgetInv.corrRDedup (cfgR : ConfigR St Msg C) (P : Party)
    {qAdv K m : ℕ} {s : SM.GameState St Msg C} (h : SMBudgetInv qAdv K (m + 1) s) :
    ∀ r ∈ support ((Computational.Proofs.GameHop.CompDedup.corrRDedup cfgR P).run s),
      SMBudgetInv qAdv K m r.2 := by
  intro r hr
  unfold Computational.Proofs.GameHop.CompDedup.corrRDedup at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
  split_ifs at hr
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact h.mono (Nat.le_succ m)
  · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
      Set.mem_singleton_iff] at hr
    subst hr; exact h.afterCorrDedup

end SMBudgetInv

/-! ## Evaluation agreement and cost bounds -/

section SpkLeakRedEval

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] {PQC : Type} [SampleableType PQC]
  (P : Params Bytes PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
  (encPt : Pt → Bytes) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (s : BitVec 256) (K B qep : ℕ)

local notation "S" => spkLeakSessionSig Pt ℓ PQC
local notation "OSM" => spkLeakSessionSmOps P ℓ decT encT
local notation "OO" => spkLeakSessionOps P ℓ Dh encPt encT decT s
local notation "II" => e2ePrfIface Pt ℓ PQC
local notation "GS" => @gsTy Pt (GhostState Bytes) Unit (CBC.Plain ℓ) PQC (BitVec 256) Bytes
local notation "RR" => @smRrTy Pt (GhostState Bytes) Unit (CBC.Plain ℓ) PQC (BitVec 256) Bytes

def sessionSchemeUPt :
    SMSchemeR Pt (GhostState Bytes) (CBC.Plain ℓ) PQC (BitVec 256) Bytes where
  initA _ := e2eInitB P (0, 0, 0, 0, 0)
  initB _ := e2eInitB P (0, 0, 0, 0, 0)
  send := (sessionSchemeU P ℓ).send
  receive := (sessionSchemeU P ℓ).receive

theorem eval_bind_ret {S' : Sig} {O' : Ops S'} {ι : Type} {T : OracleSpec ι} {I : Iface S' T}
    {Γ : List (Ty S')} {t u : Ty S'} (e : Expr O' Γ t) (k : Comp O' I (t :: Γ) u) (ρ : Env Γ) :
    (Comp.bind (.ret e) k).eval ρ = k.eval (Env.cons (e.eval ρ) ρ) :=
  pure_bind (e.eval ρ) (fun x => k.eval (Env.cons x ρ))

theorem eval_ite {S' : Sig} {O' : Ops S'} {ι : Type} {T : OracleSpec ι} {I : Iface S' T}
    {Γ : List (Ty S')} {t : Ty S'} (c : Expr O' Γ .bool) (th el : Comp O' I Γ t) (ρ : Env Γ) :
    (Comp.ite c th el).eval ρ = if c.eval ρ then th.eval ρ else el.eval ρ := rfl

theorem eval_bind {S' : Sig} {O' : Ops S'} {ι : Type} {T : OracleSpec ι} {I : Iface S' T}
    {Γ : List (Ty S')} {t u : Ty S'} (m : Comp O' I Γ t) (k : Comp O' I (t :: Γ) u) (ρ : Env Γ) :
    (Comp.bind m k).eval ρ = (m.eval ρ >>= fun x => k.eval (Env.cons x ρ)) := rfl

theorem eval_caseOpt {S' : Sig} {O' : Ops S'} {ι : Type} {T : OracleSpec ι} {I : Iface S' T}
    {Γ : List (Ty S')} {t u : Ty S'} (e : Expr O' Γ (.opt t))
    (noneB : Comp O' I Γ u) (someB : Comp O' I (t :: Γ) u) (ρ : Env Γ) :
    (Comp.caseOpt e noneB someB).eval ρ =
      match e.eval ρ with
      | none => noneB.eval ρ
      | some x => someB.eval (Env.cons x ρ) := by
  rcases h : e.eval ρ with _ | x <;> simp [Comp.eval, h]

@[simp] theorem eval_caseOpt_v0_none {S' : Sig} {O' : Ops S'} {ι : Type} {T : OracleSpec ι}
    {I : Iface S' T} {Γ : List (Ty S')} {t u : Ty S'}
    (noneB : Comp O' I (t.opt :: Γ) u) (someB : Comp O' I (t :: t.opt :: Γ) u) (ρ : Env Γ) :
    (Comp.caseOpt .v0 noneB someB).eval (.cons none ρ) = noneB.eval (.cons none ρ) := rfl

@[simp] theorem eval_caseOpt_v0_some {S' : Sig} {O' : Ops S'} {ι : Type} {T : OracleSpec ι}
    {I : Iface S' T} {Γ : List (Ty S')} {t u : Ty S'} (x : t.denote)
    (noneB : Comp O' I (t.opt :: Γ) u) (someB : Comp O' I (t :: t.opt :: Γ) u) (ρ : Env Γ) :
    (Comp.caseOpt .v0 noneB someB).eval (.cons (some x) ρ) =
      someB.eval (.cons x (.cons (some x) ρ)) := rfl

theorem eval_ret {S' : Sig} {O' : Ops S'} {ι : Type} {T : OracleSpec ι} {I : Iface S' T}
    {Γ : List (Ty S')} {t : Ty S'} (e : Expr O' Γ t) (ρ : Env Γ) :
    (Comp.ret (I := I) e).eval ρ = pure (e.eval ρ) := rfl

theorem eqCt_bytes_eq :
    ((· == ·) : Bytes → Bytes → Bool) =
      @BEq.beq Bytes (@instBEqOfDecidableEq Bytes inferInstance) := by
  funext a b
  exact Bool.eq_iff_iff.mpr (beq_iff_eq.trans decide_eq_true_iff.symm)

theorem liftM_unif_query_bind {κ : Type} {G : OracleSpec κ} {α : Type}
    (t : unifSpec.Domain) (mx : unifSpec.Range t → ProbComp α) :
    (liftM (liftM (unifSpec.query t) >>= mx) : OracleComp (unifSpec + G) α) =
      (liftM ((unifSpec + G).query (.inl t)) >>=
        fun u => (liftM (mx u) : OracleComp (unifSpec + G) α)) := by
  rw [← liftComp_eq_liftM, liftComp_bind, liftComp_liftM_query,
    liftM_eq_liftM_liftM, OracleQuery.liftM_add_left_query]
  rfl

@[simp] theorem prfIface_withSamp_liftP {S' : Sig} {k out : Ty S'} (Smp : Samplers S')
    {α : Type} (p : ProbComp α) :
    ((prfIface k out).withSamp Smp).liftP p =
      (liftM p : OracleComp (unifSpec + MACScheme.prfSpec k.denote out.denote) α) := by
  induction p using OracleComp.inductionOn with
  | pure x => simp [Iface.liftP]
  | query_bind t mx ih =>
    rw [Iface.liftP, simulateQ_query_bind, liftM_unif_query_bind]
    exact bind_congr ih

@[simp] theorem prgIface_withSamp_liftP {S' : Sig} (Smp : Samplers S')
    {α : Type} (p : ProbComp α) :
    ((prgIface S').withSamp Smp).liftP p = p := by
  induction p using OracleComp.inductionOn with
  | pure x => simp [Iface.liftP]
  | query_bind t mx ih =>
    rw [Iface.liftP, simulateQ_query_bind]
    exact bind_congr ih

omit [DecidableEq Pt] [Zero Pt] in
@[simp] theorem e2ePrfIface_liftP {α : Type} (p : ProbComp α) :
    (e2ePrfIface Pt ℓ PQC).liftP p =
      (liftM p : OracleComp (unifSpec + MACScheme.prfSpec Pt (BitVec 256)) α) :=
  prfIface_withSamp_liftP _ p

@[simp] theorem spkDrawBool_eval {Γ : List (Ty S)} (ρ : Env Γ) :
    (spkDrawBool P ℓ Dh encPt encT decT s).eval ρ =
      (liftM ($ᵗ Bool : ProbComp Bool) :
        OracleComp (unifSpec + MACScheme.prfSpec Pt (BitVec 256)) Bool) := by
  simp only [spkDrawBool, Comp.eval]
  rfl

@[simp] theorem spkDrawBv_eval {Γ : List (Ty S)} (ρ : Env Γ) :
    (spkDrawBv P ℓ Dh encPt encT decT s).eval ρ =
      (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
        OracleComp (unifSpec + MACScheme.prfSpec Pt (BitVec 256)) (BitVec 256)) := by
  simp only [spkDrawBv, Comp.eval]
  rfl

omit [DecidableEq Pt] [Zero Pt] in
theorem spkDrawCoins_eval {O' : Ops S} {Γ : List (Ty S)} (ρ : Env Γ) :
    (spkDrawCoins ℓ (Pt := Pt) (PQC := PQC) (O' := O') (Γ := Γ)).eval ρ =
      some <$> (e2ePrfIface Pt ℓ PQC).liftP ($ᵗ PQC : ProbComp PQC) := by
  simp [spkDrawCoins, Comp.eval, Expr.eval, Expr.v0,
    e2ePrfIface, Iface.withSamp, Samplers.sum, unifSamplers, map_eq_bind_pure_comp]

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem configSpkS_agrees :
    ConfigRCAgrees (Key := Pt) (St := GhostState Bytes) (St₂ := Unit) (Msg := CBC.Plain ℓ)
      (Coins := PQC) (RCoins := BitVec 256) (C := Bytes)
      (init := fun _ _ => none)
      (send := fun st m r => some ((sessionSchemeU P ℓ).send st m r))
      (receive := (sessionSchemeU P ℓ).receive)
      (eqMsg := (· == ·)) (eqCt := (· == ·))
      (stOK := fun _ _ => true) (φ := fun _ => none)
      K id (ratchetKeyAdmissible protoSignalCodec decT encT)
      (ConfigRC.spkS OSM) (configRefuseEarlyBobCorr decT encT) where
  deliverWin_eq := rfl
  r1_eq := rfl
  injectFull_eq _ _ := rfl
  challOK_eq _ _ := rfl
  challMsg_eq _ _ _ _ _ := rfl
  must_eq _ _ _ _ _ _ _ _ _ _ _ := rfl
  sendOK_eq sE pE ρ st P _ hs hp := noBobEpoch0E_eval sE pE ρ st P hs hp
  corrOK_eq sE pE ρ st P _ hs hp := by
    simp only [ConfigRC.spkS, configRefuseEarlyBobCorr, configR1OnCurve, configR1, Expr.eval,
      noSpkCorrE_eval sE pE ρ st P hs hp,
      noCorrB0E_eval sE pE ρ st P hs hp,
      noCorrBWinE_eval sE pE ρ st P hs hp,
      noAliceCorrWhileAliceBelowEpoch10, noBobCorrInEpoch0, noBobCorrWhileAliceBelowEpoch10]
  injOK_eq _ _ := rfl

theorem initAOracleC_eval {Γ : List (Ty S)}
    (ck0E sE aliceE pqrE : Expr OO Γ (.base .rcoins)) (ρ : Env Γ) :
    (initAOracleC P ℓ Dh encPt encT decT s ck0E sE aliceE pqrE).eval ρ =
      initAOracle (Pt := Pt) P Dh (ck0E.eval ρ) (sE.eval ρ) (aliceE.eval ρ) (pqrE.eval ρ) := by
  simp only [initAOracleC, Comp.eval, opInitA_eval]
  simp [initAOracle, e2eInitA, Expr.eval, Expr.v0, Expr.v1, e2ePrfIface,
    Iface.withSamp, prfIface, evalQuery]

theorem receiveB0C_eval {Γ : List (Ty S)}
    (hB_b0 : ∀ g c rc prk st' t' i' m',
      finishRecvB0 P ℓ g c rc prk = some (st', t', i', m') → t' ≤ B ∧ i' ≤ B)
    (sE : Expr OO Γ (.base .rcoins)) (gE : Expr OO Γ (.base .st))
    (cE : Expr OO Γ (.base .ct)) (rcE : Expr OO Γ (.base .rcoins)) (ρ : Env Γ)
    (hp : (gE.eval ρ).party = .B) :
    (receiveB0C P ℓ Dh encPt encT decT s B sE gE cE rcE).eval ρ =
      receiveB0 P ℓ Dh encT decT (sE.eval ρ) (gE.eval ρ) (cE.eval ρ) (rcE.eval ρ) := by
  unfold receiveB0C receiveB0
  rw [eval_bind_ret, eval_caseOpt]
  set sVal := sE.eval ρ
  set gVal := gE.eval ρ
  set cVal := cE.eval ρ
  set rcVal := rcE.eval ρ
  have hsk : (opSenderKeyPt P ℓ Dh encPt encT decT s
      (.fst (.snd (.snd (Expr.v0 (O := OO)))))).eval
      (Env.cons ((Expr.pair sE (.pair gE (.pair cE rcE))).eval ρ) ρ) =
      senderKeyPt P encT decT cVal := by
    simp [cVal, Expr.eval, Expr.v0]
  rw [hsk]
  unfold senderKeyPt
  rcases htry : SignalMessage.tryFrom P.codec cVal with _ | msg
  · simp [Comp.eval, Expr.eval]
  · simp only
    rcases hdec : decT msg.senderRatchetKey with _ | T
    · simp [Comp.eval, Expr.eval]
    · simp only
      split_ifs with hbad
      · simp [Comp.eval, Expr.eval]
      · dsimp only [Comp.eval, e2ePrfIface, Iface.withSamp, prfIface]
        have hpt : (opDh P ℓ Dh encPt encT decT s (.fst .v1) .v0).eval
            (Env.cons T (Env.cons ((Expr.pair sE (.pair gE (.pair cE rcE))).eval ρ) ρ)) =
            Dh.dh sVal T := rfl
        rw [hpt]
        refine bind_congr fun prk => ?_
        rw [opFinishRecvB0_eval]
        dsimp only [Expr.eval, Expr.v0, Expr.v2, Env.get_cons_zero, Env.get_cons_succ]
        trans (pure (finishRecvB0 P ℓ gVal cVal rcVal prk))
        · congr 1
          change (finishRecvB0 P ℓ gVal cVal rcVal prk).map
            (fun x => (x.1, min x.2.1 B, min x.2.2.1 B, x.2.2.2)) =
            finishRecvB0 P ℓ gVal cVal rcVal prk
          rcases h : finishRecvB0 P ℓ gVal cVal rcVal prk with _ | ⟨st', t', i', m'⟩
          · rfl
          · obtain ⟨htB, hiB⟩ := hB_b0 gVal cVal rcVal prk st' t' i' m' h
            simp [Nat.min_eq_left htB, Nat.min_eq_left hiB]
        · unfold finishRecvB0
          rw [htry, hp]
          dsimp only
          rcases rootCreateChain P.C ((expandPRG P.C.F).gen prk).1 msg.senderRatchetKey
              (KeyPair.generate P.C rcVal).privateKey with _ | ⟨rk2, ck2⟩
          · rfl
          · dsimp only
            rcases SessionState.tryDecryptFromRecord P.C P.spqr (P.expectedAddrs .B)
                msg .whisper rcVal _ with ⟨_ | m, s_out⟩ <;> rfl

omit [SampleableType PQC] in
theorem deliverSpk_inv
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (Q : Party) (c : Bytes) (qAdv m : ℕ)
    (hInv : SMBudgetInv qAdv K (m + 1) st) :
    ∀ r ∈ support ((deliverSpk P ℓ Dh encT decT s (Q, c)).run st),
      SMBudgetInv qAdv K m r.2 := by
  intro res hres
  unfold deliverSpk at hres
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hres
  split_ifs at hres with hwin
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hres
    subst hres; exact hInv.mono (Nat.le_succ m)
  · rcases htr : st.inTransit Q.other c with _ | r
    · simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hres
      subst hres; exact hInv.mono (Nat.le_succ m)
    · simp only [htr, stateT_run_lift_bind, mem_support_bind_iff] at hres
      obtain ⟨rc, -, out, -, hres⟩ := hres
      rcases out with _ | ⟨st', t', i', m'⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hres
        subst hres; exact hInv.mono (Nat.le_succ m)
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at hres
        subst hres; exact hInv.accept

omit [SampleableType PQC] in
theorem injectSpk_inv
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes)
    (Q : Party) (c : Bytes) (qAdv m : ℕ)
    (hInv : SMBudgetInv qAdv K (m + 1) st) :
    ∀ r ∈ support ((injectSpk P ℓ Dh encT decT qep s (Q, c)).run st),
      SMBudgetInv qAdv K m r.2 := by
  intro res hres
  unfold injectSpk at hres
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hres
  by_cases href : (st.win || (st.inTransit Q.other c).isSome || !st.safeInj 3 ||
      !ratchetKeyAdmissible protoSignalCodec decT encT c)
  · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hres
    subst hres; exact hInv.mono (Nat.le_succ m)
  · simp only [href, Bool.false_eq_true, ↓reduceIte,
      stateT_run_lift_bind, mem_support_bind_iff] at hres
    obtain ⟨rc, -, out, -, hres⟩ := hres
    rcases out with _ | ⟨st', t', i', m'⟩
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hres
      subst hres; exact hInv.mono (Nat.le_succ m)
    · dsimp only at hres
      split_ifs at hres with hqep ht
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hres
        subst hres; exact hInv.mono (Nat.le_succ m)
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at hres
        subst hres; exact hInv.accept
      · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at hres
        subst hres; exact hInv.setWin

omit [DecidableEq Pt] [Zero Pt] [SampleableType PQC] in
theorem mem_support_liftSpkGameM {α : Type}
    (m : StateT (SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) ProbComp α)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) (r : α × _) :
    r ∈ support ((liftSpkGameM (Pt := Pt) m).run st) ↔ r ∈ support (m.run st) := by
  simp only [liftSpkGameM, StateT.run_mk, ← liftComp_eq_liftM, support_liftComp]

theorem spkOracleImpl_b
    (q : (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes).Domain)
    (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes) :
    ∀ r ∈ support ((spkOracleImpl P ℓ Dh encT decT qep s q).run st), r.2.b = st.b := by
  intro r hr
  rcases q with u | ((((⟨Q, msg, optR⟩ | ⟨Q, m₀, m₁, optR⟩) | ⟨Q, c⟩) | ⟨Q, c⟩) | Q)
  · simp only [spkOracleImpl, StateT.run_lift, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hr
    obtain ⟨_, -, rfl⟩ := hr; rfl
  · rw [spkOracleImpl, mem_support_liftSpkGameM] at hr
    unfold SM.transmitR SM.transmitImpl at hr
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
    by_cases hok : !((configRefuseEarlyBobCorr decT encT).sendOK st Q)
    · simp only [hok, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; rfl
    · simp only [hok, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
        pure_bind] at hr
      by_cases hwin : st.win
      · simp only [hwin, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; rfl
      · simp only [hwin, Bool.false_eq_true, ↓reduceIte, stateT_run_monadLift_bind,
          mem_support_bind_iff] at hr
        obtain ⟨⟨coins, bad⟩, -, hr⟩ := hr
        rcases hep : st.epMgmt 3 qep Q bad with _ | s₁
        · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; rfl
        · simp only [hep, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hr
          subst hr; change s₁.b = st.b; exact epMgmt_b hep
  · rw [spkOracleImpl, mem_support_liftSpkGameM] at hr
    unfold SM.challR SM.challImpl at hr
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
    by_cases hok : !((configRefuseEarlyBobCorr decT encT).sendOK st Q)
    · simp only [hok, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; rfl
    · simp only [hok, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
        pure_bind] at hr
      by_cases hwin : st.win
      · simp only [hwin, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; rfl
      · simp only [hwin, Bool.false_eq_true, ↓reduceIte, stateT_run_monadLift_bind,
          mem_support_bind_iff] at hr
        obtain ⟨⟨coins, bad⟩, -, hr⟩ := hr
        rcases hep : st.epMgmt 3 qep Q bad with _ | s₁
        · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; rfl
        · simp only [hep] at hr
          by_cases hch : (!s₁.safeCh 3 Q ||
              !(configRefuseEarlyBobCorr (St := GhostState Bytes) (Msg := CBC.Plain ℓ)
                decT encT).base.challAllowedIn (s₁.epoch Q))
          · simp only [hch, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
            subst hr; rfl
          · simp only [hch, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
              StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at hr
            subst hr; change s₁.b = st.b; exact epMgmt_b hep
  · simp only [spkOracleImpl] at hr
    unfold deliverSpk at hr
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
    split_ifs at hr
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr; subst hr; rfl
    · rcases htr : st.inTransit Q.other c with _ | rec_
      · simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr; subst hr; rfl
      · simp only [htr, stateT_run_lift_bind, mem_support_bind_iff] at hr
        obtain ⟨rc, -, out, -, hr⟩ := hr
        rcases out with _ | ⟨st', t', i', m'⟩
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr; subst hr; rfl
        · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hr
          subst hr; rfl
  · simp only [spkOracleImpl] at hr
    unfold injectSpk at hr
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
    by_cases href : (st.win || (st.inTransit Q.other c).isSome || !st.safeInj 3 ||
        !ratchetKeyAdmissible protoSignalCodec decT encT c)
    · simp only [href, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; rfl
    · simp only [href, Bool.false_eq_true, ↓reduceIte,
        stateT_run_lift_bind, mem_support_bind_iff] at hr
      obtain ⟨rc, -, out, -, hr⟩ := hr
      rcases out with _ | ⟨st', t', i', m'⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr; subst hr; rfl
      · dsimp only at hr
        split_ifs at hr
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr; subst hr; rfl
        · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hr
          subst hr; rfl
        · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff] at hr
          subst hr; rfl
  · rw [spkOracleImpl, mem_support_liftSpkGameM] at hr
    unfold SM.corrR at hr
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hr
    split_ifs at hr
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr; subst hr; rfl
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, support_pure,
        Set.mem_singleton_iff] at hr
      subst hr; rfl

theorem simulateQ_spkOracleImpl_b {α : Type}
    (oa : OracleComp (unifSpec + SM.spec (GhostState Bytes) (CBC.Plain ℓ) PQC Bytes) α) :
    ∀ (st : SM.GameState (GhostState Bytes) (CBC.Plain ℓ) Bytes),
      ∀ r ∈ support ((simulateQ (spkOracleImpl P ℓ Dh encT decT qep s) oa).run st),
        r.2.b = st.b := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro st r hr
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr; rfl
  | query_bind q mx ih =>
    intro st r hr
    rw [run_simulateQ_query_bind, mem_support_bind_iff] at hr
    obtain ⟨⟨u, s'⟩, hst, hr⟩ := hr
    exact (ih u s' r hr).trans (spkOracleImpl_b P ℓ Dh encT decT s qep q st (u, s') hst)

theorem liftM_sample_prod_bind_bv256 {κ : Type} {G : OracleSpec κ} {γ : Type}
    (f : BitVec 256 × BitVec 256 → OracleComp (unifSpec + G) γ) :
    ((liftM ($ᵗ (BitVec 256 × BitVec 256) : ProbComp (BitVec 256 × BitVec 256)) :
        OracleComp (unifSpec + G) (BitVec 256 × BitVec 256)) >>= f) =
      ((liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
          OracleComp (unifSpec + G) (BitVec 256)) >>= fun a =>
        (liftM ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) :
          OracleComp (unifSpec + G) (BitVec 256)) >>= fun b => f (a, b)) := by
  rw [SampleableType.uniformSample_prod_eq_bind (BitVec 256) (BitVec 256)]
  simp [← liftComp_eq_liftM, liftComp_bind, bind_assoc]

theorem spkLeakRedProg_init_cost :
    (spkLeakRedProg P ℓ Dh encPt encT decT s K B qep).init.cost = 118 := by
  simp [spkLeakRedProg, spkDrawBool, spkDrawBv, initAOracleC, gsMk,
    e2ePrfIface, Iface.withSamp, prfIface, Samplers.sum, unifSamplers,
    Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, bits]

theorem spkLeakRedProg_finish_cost :
    (spkLeakRedProg P ℓ Dh encPt encT decT s K B qep).finish.cost = 12 := by
  simp [spkLeakRedProg, orE, boolEq, gsB, gsWin, Comp.cost, Expr.cost, Expr.v0, Expr.v1]

theorem spkLeakRedProg_totalCost (q : ℕ) :
    (spkLeakRedProg P ℓ Dh encPt encT decT s K B qep).totalCost q =
      130 + q * ((spkLeakRedProg P ℓ Dh encPt encT decT s K B qep).handle.cost + 6) := by
  simp only [CostedReduction.totalCost, spkLeakRedProg_init_cost, spkLeakRedProg_finish_cost]
  simp only [spkLeakRedProg, e2ePrfIface, Iface.withSamp, prfIface, e2eCodec, smCodec]
  rw [max_eq_right (by simp [spkOracleImplC, Comp.cost])]
  omega

end SpkLeakRedEval

end CryptoVerification.E2E.Costed

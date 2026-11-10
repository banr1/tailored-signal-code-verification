/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.LibsignalShortDefs
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RestrictedReds
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.MsgAeadCorrect
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.SessionShort.SimAndSM
import Std.Tactic.BVDecide.Normalize.Bool
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Short-message and short-wire preservation for FS-AEAD session reductions

**Checked by Lean.**

Proves that `redFSAuth`, `redFSPriv`, and `redFSPrivCoin` on `lFS` map `SendMsgsOk` to
`FSAEAD.EncMsgsOk` and preserve `GuardedFSInjectShort`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

open Ratchet LibsignalInst LibsignalSession HMAC HKDF CBC LibsignalAead SM SM.Construction
  SM.Engine CKA AEADScheme MACScheme WireAEAD FSAEAD CryptoGames.LibsignalSM.Proofs.RestrictedReds

section Defs

variable {St Msg Coins C : Type}

def badSendMsg (ok : Msg → Bool) : (unifSpec + SM.spec St Msg Coins C).Domain → Bool
  | .inr (.inl (.inl (.inl (.inl ⟨_, m, _⟩)))) => !ok m
  | .inr (.inl (.inl (.inl (.inr ⟨_, m₀, m₁, _⟩)))) => !ok m₀ || !ok m₁
  | _ => false

def SendMsgsOk (ok : Msg → Bool) (A : SM.Adversary St Msg Coins C) : Prop :=
  A.IsQueryBoundP (fun t => badSendMsg (St := St) (Coins := Coins) (C := C) ok t = true) 0

end Defs

section RedFS

open ReductionsQueries

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

abbrev ValidQ (Q : (RSpec SS RS T M E).Domain → Prop) (mo : Mode) (ok : M → Bool) : Prop :=
  ValidQGen (SS := SS) (RS := RS) (E := E) Q mo
    (fun m => ok m = true) (fun m₀ m₁ => ok m₀ = true ∧ ok m₁ = true)

export CryptoGames.LibsignalSM.Proofs.RestrictedReds
  (safePost_sampleT safeS_lift_sampleT safeS_lookupF safeS_rootFS safeS_initFS
   safeS_startSend safeS_startRecv safeS_fsRecv safeS_reveal safeS_vRecv
   safeS_deliverE safeS_injectE safeS_corrE safeS_coinsE)

variable {Q : (RSpec SS RS T M E).Domain → Prop} {mo : Mode} {ok : M → Bool}
  (hQ : ValidQ (SS := SS) (RS := RS) (E := E) Q mo ok)
  (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ) (j : ℕ)

include hQ in
theorem safeS_fsSend (ctx : Ctx Γ T Sig (Option SS) (Option RS) M E)
    (P : Party) (t : ℕ) (ssv : Option SS) (h : Header T) (m : M) (pair : Option (M × M))
    (hssv : ssv = none → h.1 = mo.tStar)
    (hm : pair = none → ok m = true)
    (hpair : ∀ m₀ m₁, pair = some (m₀, m₁) → ok m₀ = true ∧ ok m₁ = true) :
    SafeS Q (InvFS (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS) (E := E) mo.tStar)
      (fun res s => (∀ ssv' e, res = some (ssv', e) → ssv' = none → h.1 = mo.tStar) ∧
        InvFS mo.tStar s)
      ((hooksFS cka prng fs Δcka mo j).fsSend ctx P t ssv h m pair) :=
  safeS_fsSendGen hQ cka prng fs Δcka j ctx P t ssv h m pair hssv hm hpair

include hQ in
theorem safeS_vSend (ctx : Ctx Γ T Sig (Option SS) (Option RS) M E) (P : Party)
    (s : VP Γ T Sig (Option SS) (Option RS)) (hs : InvVP mo.tStar s)
    (m : M) (pair : Option (M × M)) (r : Option CCoins)
    (hm : pair = none → ok m = true)
    (hpair : ∀ m₀ m₁, pair = some (m₀, m₁) → ok m₀ = true ∧ ok m₁ = true) :
    SafeS Q (InvFS (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS) (E := E) mo.tStar)
      (fun res s' => (∀ vp' c, res = some (vp', c) → InvVP mo.tStar vp') ∧ InvFS mo.tStar s')
      (vSend (hooksFS cka prng fs Δcka mo j) ctx P s m pair r) :=
  safeS_vSendGen hQ cka prng fs Δcka j ctx P s hs m pair r hm hpair

include hQ in
theorem safeS_transmitE (q : Party × M × Option CCoins) (hok : ok q.2.1 = true) :
    SafeS Q (InvE (Γ := Γ) (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS)
      (M := M) (E := E) mo.tStar) (fun _ es => InvE mo.tStar es)
      (transmitE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep mo.policy q) :=
  safeS_transmitEGen hQ cka prng fs Δcka qep j q hok

include hQ in
theorem safeS_challE (q : Party × M × M × Option CCoins)
    (hok₀ : ok q.2.1 = true) (hok₁ : ok q.2.2.1 = true) :
    SafeS Q (InvE (Γ := Γ) (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS)
      (M := M) (E := E) mo.tStar) (fun _ es => InvE mo.tStar es)
      (challE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep mo.cfg mo.policy q) :=
  safeS_challEGen hQ cka prng fs Δcka qep j q ⟨hok₀, hok₁⟩

include hQ in
theorem safePost_runFS (b : Bool) (B : SchemeAdversary Γ T Sig SS RS M CCoins E)
    (hok : SendMsgsOk ok B) :
    SafePost Q (fun _ => True) (runFS cka prng fs lam Δcka qep mo j b B) :=
  safePost_runFSGen hQ cka prng fs lam Δcka qep j b B hok
    (fun q hpt => by simpa [badSendMsg] using hpt)
    (fun q hpt => by simpa [badSendMsg, Bool.or_eq_true] using hpt)

theorem safePost_redFSAuth {Q : (RSpec SS RS T M E).Domain → Prop} {ok : M → Bool}
    (tL : Option ℕ) (t : ℕ)
    (hQ : ValidQ (SS := SS) (RS := RS) (E := E) Q ⟨true, tL, t⟩ ok)
    (B : SchemeAdversary Γ T Sig SS RS M CCoins E)
    (hok : SendMsgsOk ok B) :
    SafePost Q (fun _ => True) (redFSAuth cka prng fs lam Δcka qep j tL t B) :=
  safePost_redFSAuthGen cka prng fs lam Δcka qep j tL t hQ B hok
    (fun q hpt => by simpa [badSendMsg] using hpt)
    (fun q hpt => by simpa [badSendMsg, Bool.or_eq_true] using hpt)

theorem safePost_redFSPriv {Q : (RSpec SS RS T M E).Domain → Prop} {ok : M → Bool}
    (tL : Option ℕ) (t : ℕ)
    (hQ : ValidQ (SS := SS) (RS := RS) (E := E) Q ⟨false, tL, t⟩ ok)
    (B : SchemeAdversary Γ T Sig SS RS M CCoins E)
    (hok : SendMsgsOk ok B) :
    SafePost Q (fun _ => True) (redFSPriv cka prng fs lam Δcka qep tL t B) :=
  safePost_redFSPrivGen cka prng fs lam Δcka qep tL t hQ B hok
    (fun q hpt => by simpa [badSendMsg] using hpt)
    (fun q hpt => by simpa [badSendMsg, Bool.or_eq_true] using hpt)

theorem safePost_redFSPrivCoin {Q : (RSpec SS RS T M E).Domain → Prop} {ok : M → Bool}
    (tL : Option ℕ) (t : ℕ)
    (hQ : ValidQ (SS := SS) (RS := RS) (E := E) Q ⟨false, tL, t⟩ ok)
    (B : SchemeAdversary Γ T Sig SS RS M CCoins E)
    (hok : SendMsgsOk ok B) :
    SafePost Q (fun _ => True) (redFSPrivCoin cka prng fs lam Δcka qep tL t B) :=
  safePost_redFSPrivCoinGen cka prng fs lam Δcka qep tL t hQ B hok
    (fun q hpt => by simpa [badSendMsg] using hpt)
    (fun q hpt => by simpa [badSendMsg, Bool.or_eq_true] using hpt)

theorem validQ_encBadMsg (mo : Mode) (ok : M → Bool) :
    ValidQ (SS := SS) (RS := RS) (T := T) (M := M) (E := E)
      (fun t => FSAEAD.encBadMsg (SS := SS) (RS := RS) (AD := Header T) (C := E) ok t = true)
      mo ok where
  u _ := by simp [FSAEAD.encBadMsg]
  cs := by simp [FSAEAD.encBadMsg]
  cr := by simp [FSAEAD.encBadMsg]
  t _ _ _ hok := by simp [FSAEAD.encBadMsg, hok]
  c _ _ _ _ hok := by simp [FSAEAD.encBadMsg, hok.1, hok.2]
  d _ _ _ := by simp [FSAEAD.encBadMsg]
  i _ _ _ := by simp [FSAEAD.encBadMsg]

end RedFS

section Targets

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

theorem redFS_encMsgsOk_proof (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (maxSkip : ℕ) (lam : Pt) (qep : ℕ) (ok : LibsignalMsgPublicPart × Plain ℓ → Bool)
    (B : SM.Adversary (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (LibsignalSim.Fig8C Pt))
    (hB : SendMsgsOk ok B) (j : ℕ) (tL : Option ℕ) (t : ℕ) :
    FSAEAD.EncMsgsOk ok (redFSAuth (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C codec ℓ encT idOf maxSkip) lam 1 qep j tL t B) ∧
      FSAEAD.EncMsgsOk ok (redFSPriv (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C codec ℓ encT idOf maxSkip) lam 1 qep tL t B) ∧
      FSAEAD.EncMsgsOk ok (redFSPrivCoin (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C codec ℓ encT idOf maxSkip) lam 1 qep tL t B) :=
  ⟨SafePost.to_isQueryBoundP
    (safePost_redFSAuth (dhScheme Dh) (rootPRNG C.F encPt) (lFS C codec ℓ encT idOf maxSkip)
      lam 1 qep j tL t (validQ_encBadMsg ⟨true, tL, t⟩ ok) B hB),
   SafePost.to_isQueryBoundP
    (safePost_redFSPriv (dhScheme Dh) (rootPRNG C.F encPt) (lFS C codec ℓ encT idOf maxSkip)
      lam 1 qep tL t (validQ_encBadMsg ⟨false, tL, t⟩ ok) B hB),
   SafePost.to_isQueryBoundP
    (safePost_redFSPrivCoin (dhScheme Dh) (rootPRNG C.F encPt) (lFS C codec ℓ encT idOf maxSkip)
      lam 1 qep tL t (validQ_encBadMsg ⟨false, tL, t⟩ ok) B hB)⟩

end Targets

/-! ## Guarded short-inject preservation -/

section GuardedShort

open GuardedSafe ReductionsQueries

def FsSendShort {K SS RS T M : Type} (ok : M → Bool)
    (fs : FSAEADScheme K SS RS (Header T) M (ℕ × LibsignalCiphertextWithSalt32)) : Prop :=
  ∀ ss h m, ok m = true → (fs.send ss h m).2.2.1.1.length + 8 < 2 ^ 32

theorem lFS_fsSendShort {Pt : Type} (C : Crypto) (codec : SignalMessageProtoCodec)
    (hfit : SignalEncodeFits32 codec) (ℓ : ℕ) (hℓ : ℓ + 16 < 2 ^ 31 + 16)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (maxSkip : ℕ) :
    FsSendShort (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB)
      (lFS C codec ℓ encT idOf maxSkip) := by
  intro ss h m hm
  exact ProstMsgAeadCorrect.lAeadK_enc_length_lt C codec hfit ℓ hℓ encT idOf _ _ m.2 hm

section RedFSGuarded

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq I]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

local notation "E₀" => ℕ × LibsignalCiphertextWithSalt32

abbrev FGSafeS {σ α : Type} (P : α → Prop)
    (x : StateT σ (OracleComp (RSpec SS RS T M E₀)) α) : Prop :=
  GuardedSafeS
    (fsRespShort (SS := SS) (RS := RS) (AD := Header T) (Msg := M))
    (fsInjectLong (SS := SS) (RS := RS) (AD := Header T) (Msg := M))
    (fun _ => True) (fun a _ => P a ∧ True) x

abbrev FGSafeSTrue {σ α : Type}
    (x : StateT σ (OracleComp (RSpec SS RS T M E₀)) α) : Prop :=
  GuardedSafeS
    (fsRespShort (SS := SS) (RS := RS) (AD := Header T) (Msg := M))
    (fsInjectLong (SS := SS) (RS := RS) (AD := Header T) (Msg := M))
    (fun _ => True) (fun _ _ => True) x

theorem hQu_fsInjectLong (u : ℕ) :
    ¬ fsInjectLong (SS := SS) (RS := RS) (AD := Header T) (Msg := M) (.inl u) :=
  not_false

theorem guardedSafePost_sampleT (α : Type) [SampleableType α] :
    GuardedSafePost
      (fsRespShort (SS := SS) (RS := RS) (AD := Header T) (Msg := M))
      (fsInjectLong (SS := SS) (RS := RS) (AD := Header T) (Msg := M))
      (fun _ => True)
      (sampleT (tspec := FSpec SS RS T M E₀) α) :=
  GuardedSafePost.liftComp_unif hQu_fsInjectLong ($ᵗ α)

private theorem fgSafeS_lift_sampleT {σ : Type} (α : Type) [SampleableType α] :
    FGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M) (σ := σ)
      (StateT.lift (sampleT (tspec := FSpec SS RS T M E₀) α)) :=
  guardedSafeS_lift_true (guardedSafePost_sampleT α)

private theorem fgSafeS_lookupF (Ik : I) :
    FGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (lookupF (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS) (M := M) (E := E₀) Ik) := by
  unfold lookupF
  refine guardedSafeS_get_bind fun s _ => ?_
  cases s.table.lookup Ik with
  | some k => exact guardedSafeS_pure_true k
  | none =>
    refine guardedSafeS_bind_true (fgSafeS_lift_sampleT K) fun k => ?_
    exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial)
      fun _ => guardedSafeS_pure_true k

private theorem fgSafeS_isExt (j : ℕ) (Ik : I) :
    FGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (isExt (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS) (M := M) (E := E₀) j Ik) := by
  unfold isExt
  refine guardedSafeS_get_bind fun _ _ => ?_
  split
  · exact guardedSafeS_pure_true _
  · exact guardedSafeS_bind_true (guardedSafeS_set_true _ fun _ _ => trivial)
      fun _ => guardedSafeS_pure_true _

private theorem fgSafeS_extOf (j : ℕ) (sid : Option I) :
    FGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (extOf (T := T) (Sig := Sig) (K := K) (I := I) (SS := SS) (RS := RS) (M := M) (E := E₀) j sid) := by
  unfold extOf
  cases sid with
  | none => exact guardedSafeS_pure_true false
  | some Ik => exact fgSafeS_isExt j Ik

private theorem fgSafeS_rootFS (prng : PRFPRNG KR Sig I K) (mo : Mode) (t : ℕ) (Ik : I) (σ : Sig) :
    FGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (rootFS (T := T) (K := K) (SS := SS) (RS := RS) (M := M) (E := E₀) prng mo t Ik σ) := by
  unfold rootFS
  split
  · exact guardedSafeS_pure_true _
  · split
    · split
      · refine guardedSafeS_bind_true (fgSafeS_lift_sampleT I) fun _ => ?_
        refine guardedSafeS_bind_true (fgSafeS_lift_sampleT K) fun _ => ?_
        exact guardedSafeS_pure_true _
      · refine guardedSafeS_bind_true (fgSafeS_lookupF Ik) fun _ => ?_
        exact guardedSafeS_pure_true _
    · split
      · refine guardedSafeS_bind_true (fgSafeS_lift_sampleT I) fun _ => ?_
        exact guardedSafeS_pure_true _
      · exact guardedSafeS_pure_true _

theorem fgSafeS_initFS (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E₀) (lam : I) (mo : Mode) (j : ℕ) :
    FGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (initFS cka prng fs lam mo j) := by
  unfold initFS
  refine guardedSafeS_bind_true (fgSafeS_lift_sampleT KR) fun kr => ?_
  refine guardedSafeS_bind_true (fgSafeS_lift_sampleT KC) fun kc => ?_
  refine guardedSafeS_bind_true (fgSafeS_rootFS prng mo 0 lam (prng.init kr)) fun p => ?_
  refine guardedSafeS_bind_true (fgSafeS_extOf j p.2.2) fun _ => ?_
  exact guardedSafeS_pure_true _

private theorem fgSafeS_startSend (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E₀) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (ctx : Ctx Γ T Sig (Option SS) (Option RS) M E₀) (P : Party) (t : ℕ) (γ : Γ) (σ : Sig)
    (r : Option CCoins) :
    FGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      ((hooksFS cka prng fs Δcka mo j).startSend ctx P t γ σ r) := by
  dsimp only [hooksFS]
  have hbody : ∀ coins : CCoins,
      FGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
        (do
          let (σ', k, sid) ← rootFS prng mo t (cka.send γ coins).2.2 σ
          let ext ← extOf j sid
          modify fun s => { s with cache := Function.update s.cache t (some ((cka.send γ coins).2.1, σ', k, ext)) }
          return some ((cka.send γ coins).1, (cka.send γ coins).2.1, σ', if ext then none else some (fs.initSender k))) := by
    intro coins
    refine guardedSafeS_bind_true (fgSafeS_rootFS prng mo t (cka.send γ coins).2.2 σ) fun p => ?_
    refine guardedSafeS_bind_true (fgSafeS_extOf j p.2.2) fun _ => ?_
    refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
    exact guardedSafeS_pure_true _
  cases r with
  | some coins => simp only [pure_bind]; exact hbody coins
  | none => exact guardedSafeS_bind_true (fgSafeS_lift_sampleT CCoins) hbody

private theorem fgSafeS_startRecv (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E₀) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (ctx : Ctx Γ T Sig (Option SS) (Option RS) M E₀) (P : Party) (t : ℕ) (γ : Γ) (σ : Sig)
    (Tn : T) :
    FGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      ((hooksFS cka prng fs Δcka mo j).startRecv ctx P t γ σ Tn) := by
  dsimp only [hooksFS]
  have hmiss : FGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (σ := FSState T Sig K I SS RS E₀)
      (if mo.auth && decide (t = mo.tStar) then
        if mo.tL.isSome && decide (mo.tStar = mo.tH) then pure none
        else do
          let kk := cka.receive γ Tn
          let k' ← lookupF kk.2
          let ext ← isExt j kk.2
          return some (some (kk.1, (prng.up σ kk.2).1, if ext then none else some (fs.initReceiver k')))
      else pure (some none)) := by
    split
    · split
      · exact guardedSafeS_pure_true none
      · refine guardedSafeS_bind_true (fgSafeS_lookupF (cka.receive γ Tn).2) fun _ => ?_
        refine guardedSafeS_bind_true (fgSafeS_isExt j (cka.receive γ Tn).2) fun _ => ?_
        exact guardedSafeS_pure_true _
    · exact guardedSafeS_pure_true (some none)
  refine guardedSafeS_get_bind fun s _ => ?_
  rcases s.cache t with _ | ⟨Tc, σc, k, ext⟩
  · exact hmiss
  · split
    · exact guardedSafeS_pure_true _
    · exact hmiss

private theorem fgSafeS_fsSend {ok : M → Bool}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E₀) (hfs : FsSendShort ok fs)
    (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (ctx : Ctx Γ T Sig (Option SS) (Option RS) M E₀)
    (P : Party) (t : ℕ) (ssv : Option SS) (h : Header T) (m : M) (pair : Option (M × M))
    (hm : ok m = true) :
    FGSafeS (SS := SS) (RS := RS) (T := T) (M := M)
      (fun res => ∀ (ssv' : Option SS) (e : E₀), res = some (ssv', e) → e.2.1.1.length + 8 < 2 ^ 32)
      ((hooksFS cka prng fs Δcka mo j).fsSend ctx P t ssv h m pair) := by
  dsimp only [hooksFS]
  cases ssv with
  | some ss =>
    refine guardedSafeS_pure _ fun _ _ => ⟨?_, trivial⟩
    rintro _ _ ⟨⟩
    exact hfs ss h m hm
  | none =>
    refine guardedSafeS_get_bind fun s _ => ?_
    rcases s.ext with _ | ⟨ss, rs⟩
    · by_cases hc : (!ctx.safeCh (2 + Δcka) P && !s.fsSCorr) = true
      · simp only [hc, ↓reduceIte]
        dsimp only [liftF, FSAEAD.corruptSenderQuery]
        refine guardedSafeS_bind_query (Q := fsInjectLong) not_false fun r _ => ?_
        cases r with
        | none =>
          simp only [pure_bind, Bool.not_false, ↓reduceIte]
          exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ _ ⟨⟩, trivial⟩
        | some _ =>
          refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
          simp only [pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          cases pair with
          | none =>
            dsimp only [liftF, FSAEAD.transmitQuery]
            refine guardedSafeS_bind_query (Q := fsInjectLong) not_false fun e? he? => ?_
            cases e? with
            | none => exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ _ ⟨⟩, trivial⟩
            | some e =>
              refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
              refine guardedSafeS_pure _ fun _ _ => ⟨?_, trivial⟩
              rintro _ _ ⟨⟩
              exact he? e rfl
          | some mm =>
            rcases mm with ⟨m₀, m₁⟩
            dsimp only [liftF, FSAEAD.challengeQuery]
            refine guardedSafeS_bind_query (Q := fsInjectLong) not_false fun e? he? => ?_
            cases e? with
            | none => exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ _ ⟨⟩, trivial⟩
            | some e =>
              refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
              refine guardedSafeS_pure _ fun _ _ => ⟨?_, trivial⟩
              rintro _ _ ⟨⟩
              exact he? e rfl
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, pure_bind, Bool.not_true]
        cases pair with
        | none =>
          dsimp only [liftF, FSAEAD.transmitQuery]
          refine guardedSafeS_bind_query (Q := fsInjectLong) not_false fun e? he? => ?_
          cases e? with
          | none => exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ _ ⟨⟩, trivial⟩
          | some e =>
            refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
            refine guardedSafeS_pure _ fun _ _ => ⟨?_, trivial⟩
            rintro _ _ ⟨⟩
            exact he? e rfl
        | some mm =>
          rcases mm with ⟨m₀, m₁⟩
          dsimp only [liftF, FSAEAD.challengeQuery]
          refine guardedSafeS_bind_query (Q := fsInjectLong) not_false fun e? he? => ?_
          cases e? with
          | none => exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ _ ⟨⟩, trivial⟩
          | some e =>
            refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
            refine guardedSafeS_pure _ fun _ _ => ⟨?_, trivial⟩
            rintro _ _ ⟨⟩
            exact he? e rfl
    · refine guardedSafeS_bind_true (guardedSafeS_set_true _ fun _ _ => trivial) fun _ => ?_
      refine guardedSafeS_pure _ fun _ _ => ⟨?_, trivial⟩
      rintro _ _ ⟨⟩
      exact hfs ss h m hm

theorem fgSafeS_vSend {ok : M → Bool}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E₀) (hfs : FsSendShort ok fs)
    (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (ctx : Ctx Γ T Sig (Option SS) (Option RS) M E₀) (P : Party)
    (s : VP Γ T Sig (Option SS) (Option RS))
    (m : M) (pair : Option (M × M)) (r : Option CCoins) (hm : ok m = true) :
    FGSafeS (SS := SS) (RS := RS) (T := T) (M := M)
      (fun res => ∀ vp' (c : Header T × E₀), res = some (vp', c) → c.2.2.1.1.length + 8 < 2 ^ 32)
      (vSend (hooksFS cka prng fs Δcka mo j) ctx P s m pair r) := by
  unfold vSend
  have hdef : (default : E₀).2.1.1.length + 8 < 2 ^ 32 := by decide
  by_cases h1 : s.id.sendsIn (s.tcur + 1) = true
  · simp only [h1, ↓reduceIte]
    refine guardedSafeS_bind_true
      (fgSafeS_startSend cka prng fs Δcka mo j ctx P (s.tcur + 1) s.γ s.root r)
      fun res => ?_
    rcases res with _ | ⟨γ', T', σ', ss⟩
    · simp only [pure_bind]
      exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ _ ⟨⟩, trivial⟩
    · simp only [pure_bind]
      refine guardedSafeS_bind_and
        (fgSafeS_fsSend cka prng fs hfs Δcka mo j ctx P (s.tcur + 1) ss (s.tcur + 1, some T') m pair hm)
        fun res' hres' => ?_
      rcases res' with _ | ⟨v', e⟩
      · exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ _ ⟨⟩, trivial⟩
      · refine guardedSafeS_pure _ fun _ _ => ⟨?_, trivial⟩
        rintro _ _ ⟨⟩
        exact hres' v' e rfl
  · simp only [h1, Bool.false_eq_true, ↓reduceIte, pure_bind]
    cases s.vS with
    | none =>
      refine guardedSafeS_pure _ fun _ _ => ⟨?_, trivial⟩
      rintro _ _ ⟨⟩
      exact hdef
    | some v =>
      refine guardedSafeS_bind_and
        (fgSafeS_fsSend cka prng fs hfs Δcka mo j ctx P s.tcur v (s.tcur, s.curCkaMsg) m pair hm)
        fun res' hres' => ?_
      rcases res' with _ | ⟨v', e⟩
      · exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ _ ⟨⟩, trivial⟩
      · refine guardedSafeS_pure _ fun _ _ => ⟨?_, trivial⟩
        rintro _ _ ⟨⟩
        exact hres' v' e rfl

private theorem fgSafeS_fsRecv (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E₀) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (ctx : Ctx Γ T Sig (Option SS) (Option RS) M E₀)
    (P : Party) (t : ℕ) (rsv : Option RS) (h : Header T) (e : E₀)
    (rec : Option (SM.Record M (Header T × E₀)))
    (he : e.2.1.1.length < 2 ^ 32) :
    FGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      ((hooksFS cka prng fs Δcka mo j).fsRecv ctx P t rsv h e rec) := by
  dsimp only [hooksFS]
  cases rsv with
  | some rs => exact guardedSafeS_pure_true _
  | none =>
    refine guardedSafeS_get_bind fun s _ => ?_
    rcases s.ext with _ | ⟨ss, rs⟩
    · dsimp only
      rcases List.find? _ s.fsTrans with _ | m0
      · simp only [Option.isSome, Bool.false_eq_true, ↓reduceIte]
        dsimp only [liftF, FSAEAD.injectQuery]
        refine guardedSafeS_bind_query (Q := fsInjectLong) (fun hlong => hlong he) fun res _ => ?_
        cases res with
        | none => exact guardedSafeS_pure_true none
        | some rr =>
          cases rr with
          | rejected => exact guardedSafeS_pure_true (some none)
          | accepted i mo' =>
            refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
            cases mo' <;> cases rec <;> exact guardedSafeS_pure_true _
      · simp only [Option.isSome, ↓reduceIte]
        dsimp only [liftF, FSAEAD.deliverQuery]
        refine guardedSafeS_bind_query (Q := fsInjectLong) not_false fun res _ => ?_
        cases res with
        | none => exact guardedSafeS_pure_true none
        | some rr =>
          cases rr with
          | rejected => exact guardedSafeS_pure_true (some none)
          | accepted i mo' =>
            refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
            cases mo' <;> cases rec <;> exact guardedSafeS_pure_true _
    · dsimp only
      rcases fs.receive rs h e with _ | ⟨rs', i, m⟩
      · exact guardedSafeS_pure_true (some none)
      · refine guardedSafeS_bind_true (guardedSafeS_set_true _ fun _ _ => trivial) fun _ => ?_
        exact guardedSafeS_pure_true _

theorem fgSafeS_vRecv (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E₀) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (ctx : Ctx Γ T Sig (Option SS) (Option RS) M E₀) (P : Party)
    (s : VP Γ T Sig (Option SS) (Option RS))
    (c : Header T × E₀) (rec : Option (SM.Record M (Header T × E₀)))
    (hc : c.2.2.1.1.length < 2 ^ 32) :
    FGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (vRecv (hooksFS cka prng fs Δcka mo j) ctx P s c rec) := by
  unfold vRecv
  dsimp only
  split
  · exact guardedSafeS_pure_true (some none)
  · split
    · cases c.1.2 with
      | none => simp only [pure_bind]; exact guardedSafeS_pure_true (some none)
      | some Tn =>
        refine guardedSafeS_bind_true
          (fgSafeS_startRecv cka prng fs Δcka mo j ctx P c.1.1 s.γ s.root Tn) fun res => ?_
        rcases res with _ | (_ | ⟨γ', σ', rs⟩)
        · simp only [pure_bind]; exact guardedSafeS_pure_true none
        · simp only [pure_bind]; exact guardedSafeS_pure_true (some none)
        · simp only [pure_bind, Function.update_self]
          refine guardedSafeS_bind_true
            (fgSafeS_fsRecv cka prng fs Δcka mo j ctx P c.1.1 rs c.1 c.2 rec hc) fun res' => ?_
          rcases res' with _ | (_ | ⟨v', i, m⟩) <;> exact guardedSafeS_pure_true _
    · simp only [pure_bind]
      cases s.vR c.1.1 with
      | none => exact guardedSafeS_pure_true (some none)
      | some v =>
        refine guardedSafeS_bind_true
          (fgSafeS_fsRecv cka prng fs Δcka mo j ctx P c.1.1 v c.1 c.2 rec hc) fun res' => ?_
        rcases res' with _ | (_ | ⟨v', i, m⟩) <;> exact guardedSafeS_pure_true _

theorem fgSafeS_reveal (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E₀) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (ctx : Ctx Γ T Sig (Option SS) (Option RS) M E₀)
    (P : Party) (vp : PartyState Γ T Sig (Option SS) (Option RS)) :
    FGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      ((hooksFS cka prng fs Δcka mo j).reveal ctx P vp) := by
  dsimp only [hooksFS]
  have hrecv : ∀ vS : Option SS,
      FGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
        (σ := FSState T Sig K I SS RS E₀)
        (do
          let rsExt? : Option (Option RS) ← match vp.vR mo.tStar with
            | some none => do
              match (← get).ext with
              | some (_, rs) => pure (some (some rs))
              | none =>
                if mo.auth then pure none
                else
                  match ← liftF (FSAEAD.corruptReceiverQuery (SenderState := SS) (ReceiverState := RS)
                      (AssocData := Header T) (Message := M) (Ciphertext := E₀)) with
                  | none => pure none
                  | some (ss, rs) =>
                    modify fun s => { s with ext := some (ss, rs) }
                    pure (some (some rs))
            | _ => pure (some none)
          match rsExt? with
          | none => return none
          | some rsExt =>
            let vR : ℕ → Option RS := fun t => match vp.vR t with
              | some (some rs) => some rs
              | some none => rsExt
              | none => none
            return some (realParty vp vp.γ vp.root vS vR)) := by
    intro vS
    rcases vp.vR mo.tStar with _ | (_ | rs)
    · simp only [pure_bind]; exact guardedSafeS_pure_true _
    · refine guardedSafeS_get_bind fun s _ => ?_
      cases s.ext with
      | some sr => simp only [pure_bind]; exact guardedSafeS_pure_true _
      | none =>
        by_cases ha : mo.auth = true
        · simp only [ha, ↓reduceIte, pure_bind]; exact guardedSafeS_pure_true none
        · simp only [ha, Bool.false_eq_true, ↓reduceIte]
          dsimp only [liftF, FSAEAD.corruptReceiverQuery]
          refine guardedSafeS_bind_query (Q := fsInjectLong) not_false fun r _ => ?_
          cases r with
          | none => simp only [pure_bind]; exact guardedSafeS_pure_true none
          | some sr =>
            refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
            simp only [pure_bind]; exact guardedSafeS_pure_true _
    · simp only [pure_bind]; exact guardedSafeS_pure_true _
  rcases vp.vS with _ | (_ | ss)
  · simp only [pure_bind]; exact hrecv none
  · refine guardedSafeS_get_bind fun s _ => ?_
    cases s.ext with
    | some sr => simp only [pure_bind]; exact hrecv (some sr.1)
    | none =>
      dsimp only [liftF, FSAEAD.corruptSenderQuery]
      refine guardedSafeS_bind_query (Q := fsInjectLong) not_false fun r _ => ?_
      cases r with
      | none => simp only [pure_bind]; exact guardedSafeS_pure_true none
      | some ss =>
        refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
        simp only [pure_bind]; exact hrecv (some ss)
  · simp only [pure_bind]; exact hrecv (some ss)

theorem fgSafeS_liftH_true {α : Type}
    {x : HM (FSpec SS RS T M E₀) (FSState T Sig K I SS RS E₀) α}
    (hx : FGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M) x) :
    FGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (liftH x : EM (FSpec SS RS T M E₀) Γ T Sig (Option SS) (Option RS) M E₀
        (FSState T Sig K I SS RS E₀) α) := fun es _ => by
  unfold liftH
  exact (hx es.h trivial).bind fun _ _ => GuardedSafePost.pure trivial

theorem fgSafeS_liftH_and {α : Type} {C : α → Prop}
    {x : HM (FSpec SS RS T M E₀) (FSState T Sig K I SS RS E₀) α}
    (hx : FGSafeS (SS := SS) (RS := RS) (T := T) (M := M) C x) :
    FGSafeS (SS := SS) (RS := RS) (T := T) (M := M) C
      (liftH x : EM (FSpec SS RS T M E₀) Γ T Sig (Option SS) (Option RS) M E₀
        (FSState T Sig K I SS RS E₀) α) := fun es _ => by
  unfold liftH
  exact (hx es.h trivial).bind fun p hp => GuardedSafePost.pure ⟨hp.1, trivial⟩

theorem fgSafeS_abortE :
    FGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (abortE : EM (FSpec SS RS T M E₀) Γ T Sig (Option SS) (Option RS) M E₀
        (FSState T Sig K I SS RS E₀) Unit) := by
  unfold abortE
  exact guardedSafeS_modify_true _ fun _ _ => trivial

theorem fgSafeS_commitE (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E₀) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (s : Ctx Γ T Sig (Option SS) (Option RS) M E₀) (P : Party)
    (old new : VP Γ T Sig (Option SS) (Option RS)) (pos : SM.Pos) :
    FGSafeSTrue (SS := SS) (RS := RS) (T := T) (M := M)
      (commitE (hooksFS cka prng fs Δcka mo j) s P old new pos) := by
  unfold commitE
  dsimp only [hooksFS]
  refine guardedSafeS_bind_true (fgSafeS_liftH_true (guardedSafeS_pure_true (some new))) fun res => ?_
  cases res with
  | none => exact guardedSafeS_bind_true fgSafeS_abortE fun _ => guardedSafeS_pure_true none
  | some _ => exact guardedSafeS_pure_true _

private theorem mode_cfg_challMsg_eq_none (mo : Mode) (t : ℕ) :
    (mo.cfg (M := M)).challMsg t = none := by
  unfold Mode.cfg Config.auth SM.Config.priv
  split <;> rfl

theorem fgSafeS_transmitE {ok : M → Bool}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E₀) (hfs : FsSendShort ok fs)
    (Δcka qep : ℕ) (mo : Mode) (j : ℕ)
    (q : Party × M × Option CCoins) (hok : ok q.2.1 = true) :
    FGSafeS (SS := SS) (RS := RS) (T := T) (M := M)
      (fun res => ∀ c : Header T × E₀, res = some c → c.2.2.1.1.length + 8 < 2 ^ 32)
      (transmitE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep mo.policy q) := by
  rcases q with ⟨P, m, r⟩
  unfold transmitE
  refine guardedSafeS_get_bind fun es _ => ?_
  by_cases h1 : (es.abort || es.g.win) = true
  · simp only [h1, ↓reduceIte]
    exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases es.g.epMgmt (2 + Δcka) qep P r.isSome with
    | none => exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
    | some s₁ =>
      by_cases h2 : mo.policy.leakDoom es.g s₁ = true
      · simp only [h2, ↓reduceIte]
        exact guardedSafeS_bind_true fgSafeS_abortE fun _ =>
          guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
      · simp only [h2, Bool.false_eq_true, ↓reduceIte]
        refine guardedSafeS_bind_and
          (fgSafeS_liftH_and (fgSafeS_vSend cka prng fs hfs Δcka mo j s₁ P (s₁.st P) m none r hok))
          fun res hres => ?_
        rcases res with _ | ⟨st', c⟩
        · exact guardedSafeS_bind_true fgSafeS_abortE fun _ =>
            guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
        · refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
          refine guardedSafeS_pure (some c) fun _ _ => ⟨?_, trivial⟩
          rintro _ ⟨⟩
          exact hres st' c rfl

theorem fgSafeS_challE {ok : M → Bool}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E₀) (hfs : FsSendShort ok fs)
    (Δcka qep : ℕ) (mo : Mode) (j : ℕ)
    (q : Party × M × M × Option CCoins)
    (hok₀ : ok q.2.1 = true) (hok₁ : ok q.2.2.1 = true) :
    FGSafeS (SS := SS) (RS := RS) (T := T) (M := M)
      (fun res => ∀ c : Header T × E₀, res = some c → c.2.2.1.1.length + 8 < 2 ^ 32)
      (challE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep mo.cfg mo.policy q) := by
  rcases q with ⟨P, m₀, m₁, r⟩
  unfold challE
  refine guardedSafeS_get_bind fun es _ => ?_
  by_cases h1 : (es.abort || es.g.win) = true
  · simp only [h1, ↓reduceIte]
    exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases es.g.epMgmt (2 + Δcka) qep P r.isSome with
    | none => exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
    | some s₁ =>
      by_cases h2 : (!s₁.safeCh (2 + Δcka) P || !(mo.cfg (M := M)).challAllowedIn (s₁.epoch P)) = true
      · simp only [h2, ↓reduceIte]
        exact guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
      · simp only [h2, Bool.false_eq_true, ↓reduceIte]
        by_cases h3 : mo.policy.leakDoom es.g s₁ = true
        · simp only [h3, ↓reduceIte]
          exact guardedSafeS_bind_true fgSafeS_abortE fun _ =>
            guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
        · simp only [h3, Bool.false_eq_true, ↓reduceIte]
          have hm : ok (((mo.cfg (M := M)).challMsg (s₁.epoch P)).getD (if es.g.b then m₁ else m₀)) = true := by
            rw [mode_cfg_challMsg_eq_none]
            dsimp only [Option.getD]
            cases es.g.b <;> assumption
          refine guardedSafeS_bind_and
            (fgSafeS_liftH_and (fgSafeS_vSend cka prng fs hfs Δcka mo j s₁ P (s₁.st P) _ (some (m₀, m₁)) r hm))
            fun res hres => ?_
          rcases res with _ | ⟨st', c⟩
          · exact guardedSafeS_bind_true fgSafeS_abortE fun _ =>
              guardedSafeS_pure none fun _ _ => ⟨by rintro _ ⟨⟩, trivial⟩
          · refine guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ => ?_
            refine guardedSafeS_pure (some c) fun _ _ => ⟨?_, trivial⟩
            rintro _ ⟨⟩
            exact hres st' c rfl

theorem fgSafeS_deliverE (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E₀) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (q : Party × (Header T × E₀)) (hc : q.2.2.2.1.1.length < 2 ^ 32) :
    FGSafeS (SS := SS) (RS := RS) (T := T) (M := M) (fun _ => True)
      (deliverE (hooksFS cka prng fs Δcka mo j) fs.maxSkip mo.cfg q) := by
  rcases q with ⟨P, c⟩
  unfold deliverE
  refine guardedSafeS_get_bind fun es _ => ?_
  by_cases h1 : (es.abort || es.g.win) = true
  · simp only [h1, ↓reduceIte]
    exact guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    cases es.g.inTransit P.other c with
    | none => exact guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
    | some r =>
      refine guardedSafeS_bind_true
        (fgSafeS_liftH_true (fgSafeS_vRecv cka prng fs Δcka mo j es.g P (es.g.st P) c (some r) hc))
        fun res => ?_
      rcases res with _ | (_ | ⟨st', t', i', m'⟩)
      · exact guardedSafeS_bind_true fgSafeS_abortE fun _ =>
          guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
      · by_cases h2 : ((mo.cfg (M := M)).deliverWin && es.g.mustBeCorrect fs.maxSkip P r) = true
        · simp only [h2, ↓reduceIte]
          exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ =>
            guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩
        · simp only [h2, Bool.false_eq_true, ↓reduceIte, pure_bind]
          exact guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩
      · refine guardedSafeS_bind_true
          (fgSafeS_commitE cka prng fs Δcka mo j es.g P (es.g.st P) st' r.pos)
          fun s₁? => ?_
        cases s₁? with
        | none => exact guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
        | some s₁ =>
          exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ =>
            guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩

theorem fgSafeS_injectE (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E₀) (Δcka qep : ℕ) (mo : Mode) (j : ℕ)
    (q : Party × (Header T × E₀)) (hc : q.2.2.2.1.1.length < 2 ^ 32) :
    FGSafeS (SS := SS) (RS := RS) (T := T) (M := M) (fun _ => True)
      (injectE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep mo.cfg q) := by
  rcases q with ⟨P, c⟩
  unfold injectE
  refine guardedSafeS_get_bind fun es _ => ?_
  by_cases h1 :
      (es.abort || es.g.win || (es.g.inTransit P.other c).isSome || !es.g.safeInj (2 + Δcka)) = true
  · simp only [h1, ↓reduceIte]
    exact guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    refine guardedSafeS_bind_true
      (fgSafeS_liftH_true (fgSafeS_vRecv cka prng fs Δcka mo j es.g P (es.g.st P) c none hc))
      fun res => ?_
    rcases res with _ | (_ | ⟨st', t', i', m'⟩)
    · exact guardedSafeS_bind_true fgSafeS_abortE fun _ =>
        guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
    · exact guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩
    · by_cases h2 : qep + 1 < t'
      · simp only [h2, ↓reduceIte]
        exact guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩
      · simp only [h2, ↓reduceIte]
        by_cases h3 : es.g.trivial (2 + Δcka) ⟨P.other, t', i'⟩ = true
        · simp only [h3, ↓reduceIte]
          refine guardedSafeS_bind_true
            (fgSafeS_commitE cka prng fs Δcka mo j es.g P (es.g.st P) st' ⟨P.other, t', i'⟩)
            fun s₁? => ?_
          cases s₁? with
          | none => exact guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
          | some s₁ =>
            exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ =>
              guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩
        · simp only [h3, Bool.false_eq_true, ↓reduceIte]
          by_cases h4 : (mo.cfg (M := M)).injectFull t' = true
          · simp only [h4, ↓reduceIte]
            exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ =>
              guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩
          · simp only [h4, Bool.false_eq_true, ↓reduceIte, pure_bind]
            exact guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩

theorem fgSafeS_corrE (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E₀) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (P : Party) :
    FGSafeS (SS := SS) (RS := RS) (T := T) (M := M) (fun _ => True)
      (corrE (hooksFS cka prng fs Δcka mo j) mo.policy P) := by
  unfold corrE
  refine guardedSafeS_get_bind fun es _ => ?_
  by_cases h1 : (es.abort || es.g.win || !es.g.corrAllowed P) = true
  · simp only [h1, ↓reduceIte]
    exact guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (mo.policy.leakDoom es.g (es.g.afterCorr P) || mo.policy.corrDoom es.g P) = true
    · simp only [h2, ↓reduceIte]
      exact guardedSafeS_bind_true fgSafeS_abortE fun _ =>
        guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      refine guardedSafeS_bind_true
        (fgSafeS_liftH_true (fgSafeS_reveal cka prng fs Δcka mo j es.g P (es.g.st P)))
        fun res => ?_
      cases res with
      | none => exact guardedSafeS_bind_true fgSafeS_abortE fun _ =>
          guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
      | some st =>
        exact guardedSafeS_bind_true (guardedSafeS_modify_true _ fun _ _ => trivial) fun _ =>
          guardedSafeS_pure (some st) fun _ _ => ⟨trivial, trivial⟩

theorem fgSafeS_coinsE (n : ℕ) :
    FGSafeS (SS := SS) (RS := RS) (T := T) (M := M) (fun _ => True)
      (coinsE n : EM (FSpec SS RS T M E₀) Γ T Sig (Option SS) (Option RS) M E₀
        (FSState T Sig K I SS RS E₀) (Fin (n + 1))) :=
  fun _ _ => (GuardedSafePost.query (hQu_fsInjectLong n)).bind fun _ _ =>
    GuardedSafePost.pure ⟨trivial, trivial⟩

theorem guardedSafePost_runFS {ok : M → Bool}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E₀) (hfs : FsSendShort ok fs)
    (lam : I) (Δcka qep : ℕ) (mo : Mode) (j : ℕ) (b : Bool)
    (B : SchemeAdversary Γ T Sig SS RS M CCoins E₀)
    (hok : SendMsgsOk ok B) (hg : SimAndSM.GuardedSMShort B) :
    GuardedSafePost
      (fsRespShort (SS := SS) (RS := RS) (AD := Header T) (Msg := M))
      (fsInjectLong (SS := SS) (RS := RS) (AD := Header T) (Msg := M))
      (fun _ => True)
      (runFS cka prng fs lam Δcka qep mo j b B) := by
  unfold runFS engRun
  refine (fgSafeS_initFS cka prng fs lam mo j {} trivial).bind fun p _ => ?_
  rcases p with ⟨vs, h⟩
  rcases vs with _ | ⟨vA, vB⟩
  · exact GuardedSafePost.pure trivial
  · have hB := hg.and_isQueryBoundP hok
    have hsim : GuardedSafePost fsRespShort fsInjectLong (fun _ => True)
        ((simulateQ (implE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep fs.maxSkip mo.cfg
          mo.policy) B).run
          { g := { st := fun P => match P with | .A => vA | .B => vB, b }, h }) := by
      refine GuardedSafePost.simulateQ_run (I := fun _ => True) hB ?_ trivial
      rintro (u | t) hpt
      · exact fgSafeS_coinsE u
      · rcases t with ((((q | q) | q) | q) | P)
        · have hok_q : ok q.2.1 = true := by
            have hnb : ¬ badSendMsg (St := PartyState Γ T Sig SS RS) (Coins := CCoins)
                (C := Header T × E₀) ok (.inr (.inl (.inl (.inl (.inl q))))) = true :=
              fun hb => hpt (Or.inr hb)
            simpa [badSendMsg] using hnb
          exact fgSafeS_transmitE cka prng fs hfs Δcka qep mo j q hok_q
        · have hok_q : ok q.2.1 = true ∧ ok q.2.2.1 = true := by
            have hnb : ¬ badSendMsg (St := PartyState Γ T Sig SS RS) (Coins := CCoins)
                (C := Header T × E₀) ok (.inr (.inl (.inl (.inl (.inr q))))) = true :=
              fun hb => hpt (Or.inr hb)
            simpa [badSendMsg, Bool.or_eq_true] using hnb
          exact fgSafeS_challE cka prng fs hfs Δcka qep mo j q hok_q.1 hok_q.2
        · have hc : q.2.2.2.1.1.length < 2 ^ 32 :=
            Decidable.of_not_not fun hnl => hpt (Or.inl hnl)
          exact fgSafeS_deliverE cka prng fs Δcka mo j q hc
        · have hc : q.2.2.2.1.1.length < 2 ^ 32 :=
            Decidable.of_not_not fun hnl => hpt (Or.inl hnl)
          exact fgSafeS_injectE cka prng fs Δcka qep mo j q hc
        · exact fgSafeS_corrE cka prng fs Δcka mo j P
    exact hsim.bind fun _ _ => GuardedSafePost.pure (P := fun _ => True) trivial

theorem guardedFSInjectShort_redFSAuth {ok : M → Bool}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E₀) (hfs : FsSendShort ok fs)
    (lam : I) (Δcka qep j : ℕ) (tL : Option ℕ) (t : ℕ)
    (B : SchemeAdversary Γ T Sig SS RS M CCoins E₀)
    (hok : SendMsgsOk ok B) (hg : SimAndSM.GuardedSMShort B) :
    GuardedFSInjectShort (redFSAuth cka prng fs lam Δcka qep j tL t B) := by
  unfold GuardedFSInjectShort redFSAuth
  exact (guardedSafePost_runFS cka prng fs hfs lam Δcka qep ⟨true, tL, t⟩ j false B hok hg).bind
    fun _ _ => guardedSafePost_sampleT Bool

theorem guardedFSInjectShort_redFSPriv {ok : M → Bool}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E₀) (hfs : FsSendShort ok fs)
    (lam : I) (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (B : SchemeAdversary Γ T Sig SS RS M CCoins E₀)
    (hok : SendMsgsOk ok B) (hg : SimAndSM.GuardedSMShort B) :
    GuardedFSInjectShort (redFSPriv cka prng fs lam Δcka qep tL t B) := by
  unfold GuardedFSInjectShort redFSPriv
  refine (guardedSafePost_runFS cka prng fs hfs lam Δcka qep ⟨false, tL, t⟩ 0 false B hok hg).bind
    fun res _ => ?_
  rcases res with _ | ⟨b', es⟩
  · exact guardedSafePost_sampleT Bool
  · dsimp only
    split
    · exact GuardedSafePost.pure (P := fun _ => True) trivial
    · exact guardedSafePost_sampleT Bool

theorem guardedFSInjectShort_redFSPrivCoin {ok : M → Bool}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E₀) (hfs : FsSendShort ok fs)
    (lam : I) (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (B : SchemeAdversary Γ T Sig SS RS M CCoins E₀)
    (hok : SendMsgsOk ok B) (hg : SimAndSM.GuardedSMShort B) :
    GuardedFSInjectShort (redFSPrivCoin cka prng fs lam Δcka qep tL t B) := by
  unfold GuardedFSInjectShort redFSPrivCoin
  exact (guardedSafePost_runFS cka prng fs hfs lam Δcka qep ⟨false, tL, t⟩ 0 false B hok hg).bind
    fun _ _ => guardedSafePost_sampleT Bool

end RedFSGuarded

section TargetsGuarded

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

theorem redFS_guardedFSInjectShort_proof (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (codec : SignalMessageProtoCodec) (hfit : SignalEncodeFits32 codec)
    (ℓ : ℕ) (hℓ : ℓ + 16 < 2 ^ 31 + 16) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (maxSkip : ℕ) (lam : Pt) (qep : ℕ)
    (B : SM.Adversary (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (LibsignalSim.Fig8C Pt))
    (hok : SendMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB) B)
    (hg : SimAndSM.GuardedSMShort B)
    (j : ℕ) (tL : Option ℕ) (t : ℕ) :
    GuardedFSInjectShort (redFSAuth (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C codec ℓ encT idOf maxSkip) lam 1 qep j tL t B) ∧
      GuardedFSInjectShort (redFSPriv (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C codec ℓ encT idOf maxSkip) lam 1 qep tL t B) ∧
      GuardedFSInjectShort (redFSPrivCoin (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C codec ℓ encT idOf maxSkip) lam 1 qep tL t B) := by
  have hfs := lFS_fsSendShort C codec hfit ℓ hℓ encT idOf maxSkip
  exact ⟨guardedFSInjectShort_redFSAuth (dhScheme Dh) (rootPRNG C.F encPt) _ hfs lam 1 qep j tL t B hok hg,
    guardedFSInjectShort_redFSPriv (dhScheme Dh) (rootPRNG C.F encPt) _ hfs lam 1 qep tL t B hok hg,
    guardedFSInjectShort_redFSPrivCoin (dhScheme Dh) (rootPRNG C.F encPt) _ hfs lam 1 qep tL t B hok hg⟩

end TargetsGuarded

end GuardedShort

end CryptoGames.LibsignalSM.Proofs.SessionShort.FSAEADRed

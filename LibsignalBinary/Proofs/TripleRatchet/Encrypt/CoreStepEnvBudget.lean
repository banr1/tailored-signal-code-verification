/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.TripleRatchet.ChainKey.MessageKeysBudget
public import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core
public import LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import ProofLib.SepLogic.WPp

/-!
# Concrete Step Envelope & Shared Helpers for `OTR::encrypt`

Defines the sequential allocator-event envelope `OtrEncryptStepEnv`, `FitsEnv` prefix-extraction
lemmas, envelope-parametric `[LibsignalPlacement]` contracts (`otrEncryptPlacedEnvSpec`,
`otrEncryptPlacedStepSpec`), and `SepWPp` join/exit helpers for `HookRng` (block `125`) and `Coins`
(block `428`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Encrypt.CoreStepEnvBudget

open Arm64 ProofLib
open CryptoGames.HKDF (Salt)
open CryptoGames.LibsignalSession (
  Crypto OutgoingTripleRatchet ShaCompress SignalMessage
  SignalProtocolError aesCbcEncrypt
)
open CryptoVerification (LibsignalPlacement lsLogFilterAddr lsmpl)
open CryptoVerification.LibsignalTripleRatchetRepr (
  AddrGhost UuidParser otrAt protocolAddressAt
  signalMessageResultAt tapeAfter utf8 uuidTryParse
)
open CryptoVerification.LibsignalTripleRatchet (
  AesCall ChainKeyGhost GenerateKeysGhost OtrEncryptGhost
  SignalMessageNewGhost SpqrModel
  extract_withLsCodeRoLoaded optAddrAt rootStack withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.Encrypt (model_of_send_some_panic)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
  RustCliAllocBudget SeqEnv fitsEvents_append rustAllocEvents rustDeallocEvents
)
open LibsignalBinary.Heap.SpecBudget (AesEncEnv FormatInnerEnv withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.ChainKey.MessageKeysBudget (
  MessageKeysEnv messageKeysEvents
)
open LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget (
  GenerateKeysEnv generateKeysEnv_canonical
)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget (
  SignalMessageNewEnv signalMessageNewEvents
)

/-! ## 1. `ChainKey::next_chain_key` with `VmPreserved` & Concrete `OTR::encrypt` Step Envelope -/

/-- `ChainKey::next_chain_key` (Block `39`) strengthened with `VmPreserved s0 sf`
(`0` heap allocations). -/
def nextChainKeyPlacedSpec (F : ShaCompress) : Spec ChainKeyGhost :=
  withVmPreserved (CryptoVerification.LibsignalTripleRatchet.Encrypt.nextChainKeyPlacedSpec F)

/-- Optional `Vec<u8>` buffer drop envelope: `[]` when capacity is `0`, or one alignment-1
deallocation of capacity `c` with `0 < c`, `minLen ≤ c`, and `c < 2 ^ 63`. -/
def OptVecDropEnv (minLen : Nat) (evs : List AllocEvent) : Prop :=
  evs = [] ∨
    ∃ c : Nat, 0 < c ∧ minLen ≤ c ∧ c < 2 ^ 63 ∧ evs = rustDeallocEvents c 1

theorem optVecDropEnv_nil (minLen : Nat) : OptVecDropEnv minLen [] :=
  Or.inl rfl

theorem optVecDropEnv_of_cap (minLen : Nat) (cap : BitVec 64)
    (hlen : minLen ≤ cap.toNat) (hlt : cap.toNat < 2 ^ 63) :
    OptVecDropEnv minLen
      (if cap = 0#64 then [] else rustDeallocEvents cap.toNat 1) := by
  by_cases hcap : cap = 0#64
  · simp only [hcap, ↓reduceIte]
    exact Or.inl rfl
  · simp only [hcap, ↓reduceIte]
    have hpos : 0 < cap.toNat := by
      rcases Nat.eq_zero_or_pos cap.toNat with hz | hp
      · exact False.elim (hcap (BitVec.eq_of_toNat_eq hz))
      · exact hp
    exact Or.inr ⟨cap.toNat, hpos, hlen, hlt, rfl⟩

theorem freeOnlyEvs_of_optVecDropEnv {minLen : Nat} {evs : List AllocEvent}
    (h : OptVecDropEnv minLen evs) : FreeOnlyEvs evs := by
  rcases h with rfl | ⟨c, _, _, _, rfl⟩
  · exact FreeOnlyEvs.nil
  · exact FreeOnlyEvs.singleton 1 c

/-- Pointer-independent `SignalMessageNewGhost` constructed inside `OTR::encrypt` on the `some`
branch (`signalMessageNewEvents` depends only on the value fields, never on pointer fields). -/
def otrSignalMessageNewGhost (C : Crypto) (x : OtrEncryptGhost)
    (pqrKey : Salt) (pqrMsg : List (BitVec 8)) : SignalMessageNewGhost :=
  let mk := (x.ot.senderChainKey.messageKeys C.F).generateKeys C.F pqrKey
  { messageVersion := x.ot.sessionVersion
    macKeyA := 0#64
    macKey := mk.macKey
    locA := x.locA
    loc := x.loc
    remA := x.remA
    rem := x.rem
    senderRatchetKeyA := 0#64
    senderRatchetKey := x.ot.senderRatchetKey.publicKey
    counter := x.ot.senderChainKey.index
    previousCounter := x.ot.previousCounter
    ciphertextA := 0#64
    ciphertext := aesCbcEncrypt C.E mk.cipherKey mk.iv x.ptext
    senderIkA := 0#64
    senderIk := x.ot.localIdentityKey
    receiverIkA := 0#64
    receiverIk := x.ot.remoteIdentityKey
    pqRatchetA := 0#64
    pqRatchet := pqrMsg
    ret := 0#64 }

/-- Exact sequential allocator-event envelope of `OTR::encrypt`:
- On `S.send x.ot.pqrState x.rest = none`: `SendEnv` followed by `FmtEnv` (`format_inner`).
- On `S.send x.ot.pqrState x.rest = some (_, pqrKey, pqrMsg)`: `SendEnv`, `MessageKeysEnv`
  (`alloc 32`), `GenerateKeysEnv` (deallocs `seed` and `pqrKey`), AES-256-CBC PKCS#7 ciphertext
  allocation (`(x.ptext.length / 16 + 1) * 16`), `signalMessageNewEvents`, old `pqrState` drop,
  temporary ciphertext `Vec<u8>` drop, and temporary `pqrMsg` `Vec<u8>` drop. -/
def OtrEncryptStepEnv (C : Crypto) (S : SpqrModel) (uuidParse : UuidParser)
    (SendEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop :=
      fun _ _ evs => evs = [])
    (FmtEnv : List AllocEvent → Prop := FormatInnerEnv)
    (x : OtrEncryptGhost) (evs : List AllocEvent) : Prop :=
  match S.send x.ot.pqrState x.rest with
  | none => SeqEnv (SendEnv x.ot.pqrState x.rest) FmtEnv evs
  | some (_newPqrState, pqrKey, pqrMsg) =>
    let mk := (x.ot.senderChainKey.messageKeys C.F).generateKeys C.F pqrKey
    let g_gk : GenerateKeysGhost :=
      { genA := 0#64
        g := x.ot.senderChainKey.messageKeys C.F
        pqrKeyA := 0#64
        pqrKey := pqrKey
        ret := 0#64 }
    let ctext := aesCbcEncrypt C.E mk.cipherKey mk.iv x.ptext
    let ctLen := (x.ptext.length / 16 + 1) * 16
    let evs_d1 := if x.pqCap = 0#64 then [] else rustDeallocEvents x.pqCap.toNat 1
    ∃ evs_spqr evs_mk evs_gk evs_d2 evs_d3,
      SendEnv x.ot.pqrState x.rest evs_spqr ∧
      MessageKeysEnv evs_mk ∧
      GenerateKeysEnv g_gk evs_gk ∧
      OptVecDropEnv ctext.length evs_d2 ∧
      OptVecDropEnv pqrMsg.length evs_d3 ∧
      evs = evs_spqr ++ evs_mk ++ evs_gk ++
        rustAllocEvents ctLen 1 ++
        signalMessageNewEvents uuidParse (otrSignalMessageNewGhost C x pqrKey pqrMsg) ++
        evs_d1 ++ evs_d2 ++ evs_d3

/-! ## 2. `FitsEnv` Prefix/Subtrace Extraction Lemmas for `OtrEncryptStepEnv` -/

theorem fitsEnv_send_of_stepEnv {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ}
    {C : Crypto} {S : SpqrModel} {uuidParse : UuidParser}
    {SendEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {FmtEnv : List AllocEvent → Prop} {x : OtrEncryptGhost}
    (hFmtWit : ∃ evs, FmtEnv evs)
    (hfit : FitsEnv M lim st0 (OtrEncryptStepEnv C S uuidParse SendEnv FmtEnv x)) :
    FitsEnv M lim st0 (SendEnv x.ot.pqrState x.rest) := by
  intro evs_s hs
  cases hsend : S.send x.ot.pqrState x.rest with
  | none =>
    obtain ⟨evs_f, hf⟩ := hFmtWit
    have hev : OtrEncryptStepEnv C S uuidParse SendEnv FmtEnv x (evs_s ++ evs_f) := by
      simp only [OtrEncryptStepEnv, hsend]
      exact Or.inr ⟨evs_s, evs_f, rfl, hs, hf⟩
    exact ((fitsEvents_append M lim evs_s evs_f st0).mp (hfit _ hev)).1
  | some val =>
    rcases val with ⟨newPqrState, pqrKey, pqrMsg⟩
    let g_gk : GenerateKeysGhost :=
      { genA := 0#64, g := x.ot.senderChainKey.messageKeys C.F,
        pqrKeyA := 0#64, pqrKey := pqrKey, ret := 0#64 }
    let evs_gk := match pqrKey with
      | some _ => rustDeallocEvents 32 1 ++ rustDeallocEvents 32 1
      | none => rustDeallocEvents 32 1
    let ctLen := (x.ptext.length / 16 + 1) * 16
    let evs_d1 := if x.pqCap = 0#64 then [] else rustDeallocEvents x.pqCap.toNat 1
    let suf := messageKeysEvents ++ evs_gk ++ rustAllocEvents ctLen 1 ++
      signalMessageNewEvents uuidParse (otrSignalMessageNewGhost C x pqrKey pqrMsg) ++ evs_d1
    have hev : OtrEncryptStepEnv C S uuidParse SendEnv FmtEnv x (evs_s ++ suf) := by
      simp only [OtrEncryptStepEnv, hsend]
      refine ⟨evs_s, messageKeysEvents, evs_gk, [], [],
        hs, rfl, generateKeysEnv_canonical g_gk,
        optVecDropEnv_nil _, optVecDropEnv_nil _, ?_⟩
      simp only [suf, ctLen, evs_d1, List.append_nil, List.append_assoc]
    exact ((fitsEvents_append M lim evs_s suf st0).mp (hfit _ hev)).1

theorem fitsEnv_fmt_of_stepEnv_none {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ}
    {C : Crypto} {S : SpqrModel} {uuidParse : UuidParser}
    {SendEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {FmtEnv : List AllocEvent → Prop} {x : OtrEncryptGhost} {evs_s : List AllocEvent}
    (hsend : S.send x.ot.pqrState x.rest = none)
    (hs : SendEnv x.ot.pqrState x.rest evs_s)
    (hfit : FitsEnv M lim st0 (OtrEncryptStepEnv C S uuidParse SendEnv FmtEnv x)) :
    FitsEnv M lim (M.stepEvents evs_s st0) FmtEnv := by
  intro evs_f hf
  have hev : OtrEncryptStepEnv C S uuidParse SendEnv FmtEnv x (evs_s ++ evs_f) := by
    simp only [OtrEncryptStepEnv, hsend]
    exact Or.inr ⟨evs_s, evs_f, rfl, hs, hf⟩
  exact ((fitsEvents_append M lim evs_s evs_f st0).mp (hfit _ hev)).2

theorem fitsEnv_mk_of_stepEnv_some {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ}
    {C : Crypto} {S : SpqrModel} {uuidParse : UuidParser}
    {SendEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {FmtEnv : List AllocEvent → Prop} {x : OtrEncryptGhost}
    {newPqrState : List (BitVec 8)} {pqrKey : Salt} {pqrMsg : List (BitVec 8)}
    {evs_s : List AllocEvent}
    (hsend : S.send x.ot.pqrState x.rest = some (newPqrState, pqrKey, pqrMsg))
    (hs : SendEnv x.ot.pqrState x.rest evs_s)
    (hfit : FitsEnv M lim st0 (OtrEncryptStepEnv C S uuidParse SendEnv FmtEnv x)) :
    FitsEnv M lim (M.stepEvents evs_s st0) MessageKeysEnv := by
  intro evs_mk hmk
  let g_gk : GenerateKeysGhost :=
    { genA := 0#64, g := x.ot.senderChainKey.messageKeys C.F,
      pqrKeyA := 0#64, pqrKey := pqrKey, ret := 0#64 }
  let evs_gk := match pqrKey with
    | some _ => rustDeallocEvents 32 1 ++ rustDeallocEvents 32 1
    | none => rustDeallocEvents 32 1
  let ctLen := (x.ptext.length / 16 + 1) * 16
  let evs_d1 := if x.pqCap = 0#64 then [] else rustDeallocEvents x.pqCap.toNat 1
  let suf := evs_gk ++ rustAllocEvents ctLen 1 ++
    signalMessageNewEvents uuidParse (otrSignalMessageNewGhost C x pqrKey pqrMsg) ++ evs_d1
  have hev : OtrEncryptStepEnv C S uuidParse SendEnv FmtEnv x (evs_s ++ (evs_mk ++ suf)) := by
    simp only [OtrEncryptStepEnv, hsend]
    refine ⟨evs_s, evs_mk, evs_gk, [], [],
      hs, hmk, generateKeysEnv_canonical g_gk,
      optVecDropEnv_nil _, optVecDropEnv_nil _, ?_⟩
    simp only [suf, ctLen, evs_d1, List.append_nil, List.append_assoc]
  have h1 := ((fitsEvents_append M lim evs_s (evs_mk ++ suf) st0).mp (hfit _ hev)).2
  exact ((fitsEvents_append M lim evs_mk suf _).mp h1).1

theorem fitsEnv_aes_of_stepEnv_some {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ}
    {C : Crypto} {S : SpqrModel} {uuidParse : UuidParser}
    {SendEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {FmtEnv : List AllocEvent → Prop} {x : OtrEncryptGhost}
    {newPqrState : List (BitVec 8)} {pqrKey : Salt} {pqrMsg : List (BitVec 8)}
    {evs_s evs_mk evs_gk : List AllocEvent} {g_gk : GenerateKeysGhost}
    {x_aes : AesCall}
    (hsend : S.send x.ot.pqrState x.rest = some (newPqrState, pqrKey, pqrMsg))
    (hs : SendEnv x.ot.pqrState x.rest evs_s)
    (hmk : MessageKeysEnv evs_mk)
    (hgk_pqr : g_gk.pqrKey = pqrKey)
    (hgk : GenerateKeysEnv g_gk evs_gk)
    (haes_in : x_aes.input = x.ptext)
    (hfit : FitsEnv M lim st0 (OtrEncryptStepEnv C S uuidParse SendEnv FmtEnv x)) :
    FitsEnv M lim
      (M.stepEvents evs_gk (M.stepEvents evs_mk (M.stepEvents evs_s st0)))
      (AesEncEnv x_aes) := by
  intro evs_aes haes
  rw [AesEncEnv, haes_in] at haes
  subst haes
  let g_gk0 : GenerateKeysGhost :=
    { genA := 0#64, g := x.ot.senderChainKey.messageKeys C.F,
      pqrKeyA := 0#64, pqrKey := pqrKey, ret := 0#64 }
  have hgk0 : GenerateKeysEnv g_gk0 evs_gk := by
    simpa only [GenerateKeysEnv, hgk_pqr] using hgk
  let ctLen := (x.ptext.length / 16 + 1) * 16
  let evs_d1 := if x.pqCap = 0#64 then [] else rustDeallocEvents x.pqCap.toNat 1
  let pre := evs_s ++ evs_mk ++ evs_gk
  let suf := signalMessageNewEvents uuidParse (otrSignalMessageNewGhost C x pqrKey pqrMsg) ++ evs_d1
  have hev : OtrEncryptStepEnv C S uuidParse SendEnv FmtEnv x
      (pre ++ (rustAllocEvents ctLen 1 ++ suf)) := by
    simp only [OtrEncryptStepEnv, hsend]
    refine ⟨evs_s, evs_mk, evs_gk, [], [],
      hs, hmk, hgk0, optVecDropEnv_nil _, optVecDropEnv_nil _, ?_⟩
    simp only [pre, suf, ctLen, evs_d1, List.append_nil, List.append_assoc]
  have h1 := ((fitsEvents_append M lim pre (rustAllocEvents ctLen 1 ++ suf) st0).mp (hfit _ hev)).2
  have h2 := ((fitsEvents_append M lim (rustAllocEvents ctLen 1) suf _).mp h1).1
  simpa only [pre, M.stepEvents_append] using h2

theorem fitsEnv_new_of_stepEnv_some {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ}
    {C : Crypto} {S : SpqrModel} {uuidParse : UuidParser}
    {SendEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {FmtEnv : List AllocEvent → Prop} {x : OtrEncryptGhost}
    {newPqrState : List (BitVec 8)} {pqrKey : Salt} {pqrMsg : List (BitVec 8)}
    {evs_s evs_mk evs_gk evs_aes : List AllocEvent} {g_gk : GenerateKeysGhost}
    {x_aes : AesCall} {x_new : SignalMessageNewGhost}
    (hsend : S.send x.ot.pqrState x.rest = some (newPqrState, pqrKey, pqrMsg))
    (hs : SendEnv x.ot.pqrState x.rest evs_s)
    (hmk : MessageKeysEnv evs_mk)
    (hgk_pqr : g_gk.pqrKey = pqrKey)
    (hgk : GenerateKeysEnv g_gk evs_gk)
    (haes_in : x_aes.input = x.ptext)
    (haes : AesEncEnv x_aes evs_aes)
    (hnew_ev : signalMessageNewEvents uuidParse x_new =
      signalMessageNewEvents uuidParse (otrSignalMessageNewGhost C x pqrKey pqrMsg))
    (hfit : FitsEnv M lim st0 (OtrEncryptStepEnv C S uuidParse SendEnv FmtEnv x)) :
    FitsEnv M lim
      (M.stepEvents evs_aes (M.stepEvents evs_gk (M.stepEvents evs_mk (M.stepEvents evs_s st0))))
      (SignalMessageNewEnv uuidParse x_new) := by
  intro evs_new hnew
  rw [SignalMessageNewEnv, hnew_ev] at hnew
  subst hnew
  rw [AesEncEnv, haes_in] at haes
  subst haes
  let g_gk0 : GenerateKeysGhost :=
    { genA := 0#64, g := x.ot.senderChainKey.messageKeys C.F,
      pqrKeyA := 0#64, pqrKey := pqrKey, ret := 0#64 }
  have hgk0 : GenerateKeysEnv g_gk0 evs_gk := by
    simpa only [GenerateKeysEnv, hgk_pqr] using hgk
  let ctLen := (x.ptext.length / 16 + 1) * 16
  let evs_d1 := if x.pqCap = 0#64 then [] else rustDeallocEvents x.pqCap.toNat 1
  let pre := evs_s ++ evs_mk ++ evs_gk ++ rustAllocEvents ctLen 1
  let ev_new0 := signalMessageNewEvents uuidParse (otrSignalMessageNewGhost C x pqrKey pqrMsg)
  have hev : OtrEncryptStepEnv C S uuidParse SendEnv FmtEnv x
      (pre ++ (ev_new0 ++ evs_d1)) := by
    simp only [OtrEncryptStepEnv, hsend]
    refine ⟨evs_s, evs_mk, evs_gk, [], [],
      hs, hmk, hgk0, optVecDropEnv_nil _, optVecDropEnv_nil _, ?_⟩
    simp only [pre, ev_new0, ctLen, evs_d1, List.append_nil, List.append_assoc]
  have h1 := ((fitsEvents_append M lim pre (ev_new0 ++ evs_d1) st0).mp (hfit _ hev)).2
  have h2 := ((fitsEvents_append M lim ev_new0 evs_d1 _).mp h1).1
  simpa only [pre, M.stepEvents_append] using h2

/-! ## 3. Envelope-Parametric `otrEncryptPlacedEnvSpec{F,}` & Sub-Envelope Lifting -/

/-- Envelope-parametric budget specification of `OTR::encrypt` with spatial frame `F`.
Definitionally equal (`rfl`) to `DefsBudget.otrEncryptPlacedSpecF` at `DefsBudget.OtrEncryptEnv`. -/
def otrEncryptPlacedEnvSpecF [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (EncryptEnv : OtrEncryptGhost → List AllocEvent → Prop) (F : SepProp) :
    Spec (OtrEncryptGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st (EncryptEnv x)⌝ ∗
      (CryptoVerification.LibsignalTripleRatchet.Encrypt.otrEncryptPlacedSpecF
        C (A.atState lim st s) ctl uuidParse S F).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜EncryptEnv x evs⌝ ∗
      (CryptoVerification.LibsignalTripleRatchet.Encrypt.otrEncryptPlacedSpecF
        C (A.atState lim (M.stepEvents evs st) sf) ctl uuidParse S F).post x s0 sf
  onPanic := fun (x, _) s0 sf =>
    ⌜((x.model C S uuidParse).1 = .error .panic ∨ S.sendPanics x.ot.pqrState x.rest) ∧
      s0.trace <+: sf.trace⌝ ∗
      anyHeap

/-- Envelope-parametric budget specification of `OTR::encrypt` (`F = emp`).
Definitionally equal (`rfl`) to `DefsBudget.otrEncryptPlacedSpec` at `DefsBudget.OtrEncryptEnv`. -/
def otrEncryptPlacedEnvSpec [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (EncryptEnv : OtrEncryptGhost → List AllocEvent → Prop) :
    Spec (OtrEncryptGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st (EncryptEnv x)⌝ ∗
      (CryptoVerification.LibsignalTripleRatchet.Encrypt.otrEncryptPlacedSpec
        C (A.atState lim st s) ctl uuidParse S).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜EncryptEnv x evs⌝ ∗
      (CryptoVerification.LibsignalTripleRatchet.Encrypt.otrEncryptPlacedSpec
        C (A.atState lim (M.stepEvents evs st) sf) ctl uuidParse S).post x s0 sf
  onPanic := fun (x, _) s0 sf =>
    ⌜((x.model C S uuidParse).1 = .error .panic ∨ S.sendPanics x.ot.pqrState x.rest) ∧
      s0.trace <+: sf.trace⌝ ∗
      anyHeap

abbrev otrEncryptPlacedStepSpecF [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (SendEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop :=
      fun _ _ evs => evs = [])
    (FmtEnv : List AllocEvent → Prop := FormatInnerEnv) (F : SepProp) :
    Spec (OtrEncryptGhost × M.σ) :=
  otrEncryptPlacedEnvSpecF C A lim ctl uuidParse S
    (OtrEncryptStepEnv C S uuidParse SendEnv FmtEnv) F

abbrev otrEncryptPlacedStepSpec [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (SendEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop :=
      fun _ _ evs => evs = [])
    (FmtEnv : List AllocEvent → Prop := FormatInnerEnv) :
    Spec (OtrEncryptGhost × M.σ) :=
  otrEncryptPlacedEnvSpec C A lim ctl uuidParse S
    (OtrEncryptStepEnv C S uuidParse SendEnv FmtEnv)

theorem subroutine_ok_otrEncryptPlacedEnv_framed_of_imp [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64}
    {Q : List (BitVec 8) → List (BitVec 8) → Prop} {F : SepProp}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {uuidParse : UuidParser} {S : SpqrModel}
    {Env₁ Env₂ : OtrEncryptGhost → List AllocEvent → Prop}
    (hImp : ∀ x evs, Q x.ot.pqrState x.rest → x.ptext.length < 2 ^ 32 → Env₁ x evs → Env₂ x evs)
    (h1 : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl
        { otrEncryptPlacedEnvSpec C A lim ctl uuidParse S Env₁ with
          pre := fun (x, st) s =>
            ⌜Q x.ot.pqrState x.rest⌝ ∗ F ∗
              (otrEncryptPlacedEnvSpec C A lim ctl uuidParse S Env₁).pre (x, st) s
          post := fun (x, st) s0 sf =>
            F ∗ (otrEncryptPlacedEnvSpec C A lim ctl uuidParse S Env₁).post (x, st) s0 sf })) :
    subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl
        { otrEncryptPlacedEnvSpec C A lim ctl uuidParse S Env₂ with
          pre := fun (x, st) s =>
            ⌜Q x.ot.pqrState x.rest⌝ ∗ F ∗
              (otrEncryptPlacedEnvSpec C A lim ctl uuidParse S Env₂).pre (x, st) s
          post := fun (x, st) s0 sf =>
            F ∗ (otrEncryptPlacedEnvSpec C A lim ctl uuidParse S Env₂).post (x, st) s0 sf }) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  obtain ⟨hcro, hm1⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [otrEncryptPlacedEnvSpec,
    CryptoVerification.LibsignalTripleRatchet.Encrypt.otrEncryptPlacedSpec] at hm1
  simp only [sepConj_assoc] at hm1
  rw [satisfies_pure_sepConj] at hm1
  obtain ⟨hQ, hm2⟩ := hm1
  rw [sepConj_left_comm F, satisfies_pure_sepConj] at hm2
  obtain ⟨hfit2, hm3⟩ := hm2
  rw [sepConj_left_comm F, satisfies_pure_sepConj] at hm3
  obtain ⟨hpure, hmem⟩ := hm3
  have hpt : x.ptext.length < 2 ^ 32 := hpure.2.2.2.2.1
  have hfit1 : FitsEnv M lim st (Env₁ x) :=
    FitsEnv.mono (fun evs he => hImp x evs hQ hpt he) hfit2
  have hpre1 : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        { otrEncryptPlacedEnvSpec C A lim ctl uuidParse S Env₁ with
          pre := fun (x, st) s =>
            ⌜Q x.ot.pqrState x.rest⌝ ∗ F ∗
              (otrEncryptPlacedEnvSpec C A lim ctl uuidParse S Env₁).pre (x, st) s
          post := fun (x, st) s0 sf =>
            F ∗ (otrEncryptPlacedEnvSpec C A lim ctl uuidParse S Env₁).post (x, st) s0 sf }).pre
        (x, st) s0 ∗ R := by
    dsimp only [withLsCodeRoLoaded, otrEncryptPlacedEnvSpec] at hpre ⊢
    simp only [sepConj_assoc] at hpre ⊢
    exact Satisfies.mono (sepConj_mono_right (sepConj_mono_right
      (Entails.pure_left fun _ =>
        Entails.pure_right hfit1 (Entails.refl _)))) hpre
  refine h1.mono_outcome (x, st) R s0 hpc hrun hpre1 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, otrEncryptPlacedEnvSpec] at hpost ⊢
    refine Satisfies.mono (sepConj_mono_left (sepConj_mono_right ?_)) hpost
    refine Entails.sepExists_mono fun evs => ?_
    exact Entails.pure_left fun he1 =>
      Entails.pure_right (hImp x evs hQ hpt he1) (Entails.refl _)
  · right; left; exact ⟨hpan, hpost⟩
  · right; right; left; exact ⟨code, hex, hpost⟩
  · right; right; right; exact ⟨hoom, hpost⟩

/-! ## 4. Representation, Join, Frame-Shift, Panic, & Exit Helpers -/

theorem otrAt_atState_eq_repAlloc {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (o pqCap pqPtr : BitVec 64)
    (ot : OutgoingTripleRatchet (List (BitVec 8))) :
    otrAt (A.atState lim st s) o pqCap pqPtr ot = otrAt A.repAlloc o pqCap pqPtr ot :=
  rfl

theorem optAddrAt_atState_eq_repAlloc {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (locA : BitVec 64) (loc : Option AddrGhost) :
    optAddrAt (A.atState lim st s) locA loc = optAddrAt A.repAlloc locA loc := by
  cases loc <;> rfl

theorem protocolAddressAt_atState_eq_repAlloc {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (rem : AddrGhost) (remA : BitVec 64) :
    protocolAddressAt (A.atState lim st s) rem remA = protocolAddressAt A.repAlloc rem remA :=
  rfl

theorem signalMessageResultAt_atState_eq_repAlloc {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (ctx : List (BitVec 8)) (ret : BitVec 64)
    (res : Except SignalProtocolError SignalMessage) :
    signalMessageResultAt (A.atState lim st s) ctx ret res =
      signalMessageResultAt A.repAlloc ctx ret res := by
  cases res with
  | ok _ => rfl
  | error e => cases e <;> rfl

theorem join_focus_state {prog : Program} {ret : BitVec 64} {s : State}
    {P Frame : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (Cond : State → Prop) (P1 : SepProp) (P2 : State → SepProp)
    (hf : P = P1 ∗ Frame)
    (hstep : ∀ R,
      (∀ s', Cond s' → SepWPp prog ret s' (P2 s' ∗ R) Q Qp oom) →
      SepWPp prog ret s (P1 ∗ R) Q Qp oom)
    (hcont : ∀ s', Cond s' → SepWPp prog ret s' (P2 s' ∗ Frame) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  rw [hf]
  exact hstep Frame hcont

theorem shift_frame_to_post_budget {prog : Program} {ret : BitVec 64} {s0 s1 : State}
    {F Rest R : SepProp} {Post : State → SepProp} {φ_pan : State → Prop}
    (h : ∀ R' : SepProp,
      SepWPp prog ret s1 Rest
        (fun sf P_f =>
          ((sf.mem ⊨ P_f ∗ R') → (sf.mem ⊨ Post sf ∗ R')) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R') → φ_pan sf ∧ (sf.mem ⊨ anyHeap ∗ R'))) :
    SepWPp prog ret s1 (F ∗ Rest)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ F ∗ Post sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → φ_pan sf ∧ (sf.mem ⊨ anyHeap ∗ R)) := by
  intro R0 hm hL
  have hm' : s1.mem ⊨ Rest ∗ (F ∗ R0) := by
    have heq : (F ∗ Rest) ∗ R0 = Rest ∗ (F ∗ R0) := by sep_ac_rfl
    rwa [← heq]
  obtain ⟨sf, hsteps, hout⟩ := h (F ∗ R) (F ∗ R0) hm' hL
  rcases hout with ⟨hpcf, hrunf, P_f, hmf, ⟨hq, hspf, hcsf⟩⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hoom⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, F ∗ P_f, ?_, ⟨fun hmfR => ?_, hspf, hcsf⟩⟩⟩
    · have heq : (F ∗ P_f) ∗ R0 = P_f ∗ (F ∗ R0) := by sep_ac_rfl
      rwa [heq]
    · have hmfFR : sf.mem ⊨ P_f ∗ (F ∗ R) := by
        have heq : P_f ∗ (F ∗ R) = (F ∗ P_f) ∗ R := by sep_ac_rfl
        rwa [heq]
      have hpost := hq hmfFR
      have heq : F ∗ Post sf ∗ R = Post sf ∗ (F ∗ R) := by sep_ac_rfl
      rwa [heq]
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, F ∗ P_f, ?_, fun hmfR => ?_⟩)⟩
    · have heq : (F ∗ P_f) ∗ R0 = P_f ∗ (F ∗ R0) := by sep_ac_rfl
      rwa [heq]
    · have hmfFR : sf.mem ⊨ P_f ∗ (F ∗ R) := by
        have heq : P_f ∗ (F ∗ R) = (F ∗ P_f) ∗ R := by sep_ac_rfl
        rwa [heq]
      obtain ⟨hφ, hpan'⟩ := hqp hmfFR
      refine ⟨hφ, ?_⟩
      have heq : anyHeap ∗ (F ∗ R) = (anyHeap ∗ F) ∗ R := by sep_ac_rfl
      rw [heq] at hpan'
      exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hpan'
  · exact (not_satisfies_false_sepConj hoom).elim

theorem onPanic_of_send_budget {C : Crypto} {S : SpqrModel}
    {x : OtrEncryptGhost} {s0 s1 sf : State} {F R : SepProp}
    (htr : s1.trace = s0.trace)
    (hm : sf.mem ⊨ ((⌜S.sendPanics x.ot.pqrState x.rest ∧
      s1.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (⌜((x.model C S uuidTryParse).1 = .error .panic ∨ S.sendPanics x.ot.pqrState x.rest) ∧
      s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
  refine allowPanic_frame (fun ⟨hsp, hpref⟩ => ?_) hm
  rw [htr] at hpref
  exact ⟨Or.inr hsp, hpref⟩

theorem onPanic_of_nck_budget {C : Crypto} {S : SpqrModel}
    {x : OtrEncryptGhost} {newPqrState : List (BitVec 8)} {pqrKey : Salt}
    {pqrMsg : List (BitVec 8)} {s0 s1 sf : State} {F R : SepProp}
    (hsend : S.send x.ot.pqrState x.rest = some (newPqrState, pqrKey, pqrMsg))
    (htr : s1.trace = s0.trace)
    (hm : sf.mem ⊨ ((⌜x.ot.senderChainKey.nextChainKey C.F = .error .panic ∧
      s1.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    (((x.model C S uuidTryParse).1 = .error .panic ∨ S.sendPanics x.ot.pqrState x.rest) ∧
      s0.trace <+: sf.trace) ∧ sf.mem ⊨ anyHeap ∗ R := by
  rw [← satisfies_pure_sepConj, ← sepConj_assoc]
  refine allowPanic_frame (fun ⟨hnck, hpref⟩ => ?_) hm
  rw [htr] at hpref
  exact ⟨Or.inl (model_of_send_some_panic x C S newPqrState pqrKey pqrMsg hsend hnck), hpref⟩

/-- Protected postcondition wrapper so `simp ... only [arm64_norm]` during instruction stepping
never expands `(otrEncryptPlacedEnvSpec ...).post` inside the `SepWPp` goal. -/
def otrPostBox [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (EncryptEnv : OtrEncryptGhost → List AllocEvent → Prop)
    (x : OtrEncryptGhost) (st0 : M.σ) (s0 sf : State) : SepProp :=
  (otrEncryptPlacedEnvSpec C A lim ctl uuidParse S EncryptEnv).post (x, st0) s0 sf

theorem otrPostBox_eq [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (uuidParse : UuidParser) (S : SpqrModel)
    (EncryptEnv : OtrEncryptGhost → List AllocEvent → Prop)
    (x : OtrEncryptGhost) (st0 : M.σ) (s0 sf : State) :
    (otrEncryptPlacedEnvSpec C A lim ctl uuidParse S EncryptEnv).post (x, st0) s0 sf =
      otrPostBox C A lim ctl uuidParse S EncryptEnv x st0 s0 sf :=
  rfl

theorem otrPostBox_framed_eq [LibsignalPlacement] {M : AllocCostModel}
    (Q : List (BitVec 8) → List (BitVec 8) → Prop) (F : SepProp)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (uuidParse : UuidParser) (S : SpqrModel)
    (EncryptEnv : OtrEncryptGhost → List AllocEvent → Prop)
    (x : OtrEncryptGhost) (st0 : M.σ) (s0 sf : State) :
    (withLsCodeRoLoaded lsmpl
      { otrEncryptPlacedEnvSpec C A lim ctl uuidParse S EncryptEnv with
        pre := fun (x, st) s =>
          ⌜Q x.ot.pqrState x.rest⌝ ∗ F ∗
            (otrEncryptPlacedEnvSpec C A lim ctl uuidParse S EncryptEnv).pre (x, st) s
        post := fun (x, st) s0 sf =>
          F ∗ (otrEncryptPlacedEnvSpec C A lim ctl uuidParse S EncryptEnv).post
            (x, st) s0 sf }).post (x, st0) s0 sf =
      (F ∗ otrPostBox C A lim ctl uuidParse S EncryptEnv x st0 s0 sf) :=
  rfl

theorem sepWP_done_encrypt_budget [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {ret : BitVec 64} {s0 sf : State}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {uuidParse : UuidParser} {S : SpqrModel}
    {EncryptEnv : OtrEncryptGhost → List AllocEvent → Prop}
    {x : OtrEncryptGhost} {st0 : M.σ} {evs : List AllocEvent}
    {res : Except SignalProtocolError SignalMessage}
    {ot' : OutgoingTripleRatchet (List (BitVec 8))}
    {P_f R : SepProp}
    (hpc : sf.pc = ret) (hrun : sf.status = .Running)
    (hmod : x.model C S uuidParse = (res, ot'))
    (hevs : EncryptEnv x evs)
    (hnotpan : res ≠ .error .panic)
    (htr : sf.trace = s0.trace)
    (hspatial : P_f = ((∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64,
        otrAt A.repAlloc x.o pqCap' pqPtr' ot') ∗
      signalMessageResultAt A.repAlloc (utf8 "encrypt") x.ret res ∗
      (x.ptA ↦ₛ x.ptext) ∗ optAddrAt A.repAlloc x.locA x.loc ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗
      tapeAfter ctl x.cur x.rest (S.draws x.ot.pqrState x.rest) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s0.sp rootStack ∗
      A.pool lim (M.stepEvents evs st0) sf) ∗ emp)
    (hsp : sf.sp = s0.sp) (hcs : CalleeSavedPreserved s0 sf) :
    SepWP prog ret sf P_f
      (fun sf' P_f' =>
        ((sf'.mem ⊨ P_f' ∗ R) →
          (sf'.mem ⊨ otrPostBox C A lim ctl uuidParse S EncryptEnv x st0 s0 sf' ∗ R)) ∧
        sf'.sp = s0.sp ∧ CalleeSavedPreserved s0 sf') := by
  refine SepWP.done hpc hrun ⟨fun hm => ?_, hsp, hcs⟩
  rw [hspatial] at hm
  simp only [sepConj_emp] at hm
  unfold otrPostBox otrEncryptPlacedEnvSpec
    CryptoVerification.LibsignalTripleRatchet.Encrypt.otrEncryptPlacedSpec
  dsimp only
  rw [hmod]
  dsimp only
  simp only [otrAt_atState_eq_repAlloc, signalMessageResultAt_atState_eq_repAlloc,
    optAddrAt_atState_eq_repAlloc, protocolAddressAt_atState_eq_repAlloc]
  dsimp only [RustCliAllocBudget.atState]
  refine Satisfies.mono (sepConj_mono_left (Entails.sepExists_intro evs)) ?_
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hevs, ⟨hnotpan, htr⟩, by simpa only [sepConj_assoc] using hm⟩

end LibsignalBinary.Proofs.TripleRatchet.Encrypt.CoreStepEnvBudget

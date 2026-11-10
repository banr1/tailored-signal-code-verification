/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs

/-!
# Budget-Threaded Relocatable `OTR::encrypt` Specifications

Defines allocator-event envelopes (`SpqrSendBudgetEnv`, `OtrEncryptCoreEnv`, `OtrEncryptEnv`),
budget-threaded `[LibsignalPlacement]` contracts (`otrEncryptPlacedSpecF`, `otrEncryptPlacedSpec`),
and `PhaseCreditSpec` bounds and non-vacuity witnesses over `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget

open Arm64 ProofLib
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv
   SeqEnv FreeOnlyEvs rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.Fine (fineCostModel FineStepBound)
open LibsignalBinary.Heap.Fine.ClientBounds
  (fineStepReserveOfCum fineMaxMetaAreasOfCum fineDynIvsOfCum fineMaxGroupsOfCum)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
  (fineCostModel_modelHyps fitsEnv_fineCostModel_of_phaseCredit)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open CryptoVerification.LibsignalProtoCodec (encode)
open LibsignalBinary.Heap.SpecBudget (FormatInnerEnv)
open CryptoGames.HKDF (Salt)
open CryptoGames.LibsignalSession
  (Crypto OutgoingTripleRatchet KeyPair PublicKey PrivateKey IdentityKey ChainKey aesCbcEncrypt)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost UuidParser)
open CryptoVerification.LibsignalTripleRatchet
  (OtrEncryptGhost SpqrModel withLsCodeRoLoaded)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (publicKeySerializeEvents)
open LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget (computeMacEvents)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget
  (SignalMessageNewGhost SignalMessageNewEnv signalMessageNewEvents)

/-- Non-vacuous well-formedness predicate for Rust global-allocator events. -/
def ValidRustAllocEv (ev : AllocEvent) : Prop :=
  ev.withinMaxAlloc ∧
  match ev with
  | .alloc sz => 0 < sz
  | .aligned al sz => 0 < sz ∧ ∃ k, al = 2 ^ k
  | .free al sz => 0 < sz ∧ ∃ k, al = 2 ^ k
  | .realloc al old new => 0 < old ∧ 0 < new ∧ ∃ k, al = 2 ^ k

/-- Parametric SPQR `send` allocator-event envelope (`pqrState → rest → evs → Prop`). -/
abbrev SpqrSendBudgetEnv : Type :=
  List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop

/-- Pointer-erased `SignalMessageNewGhost` carrying the exact value fields passed to
    `<SignalMessage>::new` inside `OTR::encrypt` when `S.send` returns `some (_, pqrKey, pqrMsg)`
    (`signalMessageNewEvents` does not depend on any `*A` or `ret` pointer field). -/
def otrSignalMsgGhost (C : Crypto) (ot : OutgoingTripleRatchet (List (BitVec 8)))
    (pqrKey : Salt) (pqrMsg ptext : List (BitVec 8))
    (loc : Option AddrGhost) (rem : AddrGhost) : SignalMessageNewGhost :=
  let mk := (ot.senderChainKey.messageKeys C.F).generateKeys C.F pqrKey
  { messageVersion := ot.sessionVersion
    macKeyA := 0#64
    macKey := mk.macKey
    locA := 0#64
    loc := loc
    remA := 0#64
    rem := rem
    senderRatchetKeyA := 0#64
    senderRatchetKey := ot.senderRatchetKey.publicKey
    counter := ot.senderChainKey.index
    previousCounter := ot.previousCounter
    ciphertextA := 0#64
    ciphertext := aesCbcEncrypt C.E mk.cipherKey mk.iv ptext
    senderIkA := 0#64
    senderIk := ot.localIdentityKey
    receiverIkA := 0#64
    receiverIk := ot.remoteIdentityKey
    pqRatchetA := 0#64
    pqRatchet := pqrMsg
    ret := 0#64 }

theorem signalMessageNewEvents_eq_otrSignalMsgGhost (parse : UuidParser)
    (C : Crypto) (ot : OutgoingTripleRatchet (List (BitVec 8)))
    (pqrKey : Salt) (pqrMsg ptext : List (BitVec 8))
    (loc : Option AddrGhost) (rem : AddrGhost)
    (x_new : SignalMessageNewGhost)
    (hloc : x_new.loc = loc) (hrem : x_new.rem = rem)
    (hsrk : x_new.senderRatchetKey = ot.senderRatchetKey.publicKey)
    (hctr : x_new.counter = ot.senderChainKey.index)
    (hpctr : x_new.previousCounter = ot.previousCounter)
    (hct : x_new.ciphertext = aesCbcEncrypt C.E
      ((ot.senderChainKey.messageKeys C.F).generateKeys C.F pqrKey).cipherKey
      ((ot.senderChainKey.messageKeys C.F).generateKeys C.F pqrKey).iv ptext)
    (hpqr : x_new.pqRatchet = pqrMsg) :
    signalMessageNewEvents parse x_new =
      signalMessageNewEvents parse (otrSignalMsgGhost C ot pqrKey pqrMsg ptext loc rem) := by
  cases x_new
  dsimp only at hloc hrem hsrk hctr hpctr hct hpqr
  subst hloc hrem hsrk hctr hpctr hct hpqr
  rfl

/-- Concrete allocation envelope of `OTR::encrypt` (pointer-independent core), in exact binary call
    order: `spqr::send` (`sendEnv`), followed on `none` by `FormatInnerEnv` (`[]`), and on
    `some (_, pqrKey, pqrMsg)` by `ChainKey::message_keys` + `MessageKeyGenerator::generate_keys`
    (`SeqEnv (· = rustAllocEvents 32 1) FreeOnlyEvs`), `aes_256_cbc_encrypt`, `<SignalMessage>::new`,
    and trailing temporary/old-pq deallocations (`FreeOnlyEvs`). -/
def OtrEncryptCoreEnv (C : Crypto) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (uuidParse : UuidParser)
    (ot : OutgoingTripleRatchet (List (BitVec 8)))
    (ptext : List (BitVec 8)) (loc : Option AddrGhost)
    (rem : AddrGhost) (rest : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  SeqEnv (sendEnv ot.pqrState rest)
    (fun evs' =>
      match S.send ot.pqrState rest with
      | none => FormatInnerEnv evs'
      | some (_, pqrKey, pqrMsg) =>
        SeqEnv (SeqEnv (· = rustAllocEvents 32 1) FreeOnlyEvs)
          (SeqEnv (· = rustAllocEvents ((ptext.length / 16 + 1) * 16) 1)
            (SeqEnv (SignalMessageNewEnv uuidParse (otrSignalMsgGhost C ot pqrKey pqrMsg ptext loc rem))
              FreeOnlyEvs)) evs') evs

/-- Concrete allocation envelope of `OTR::encrypt` on `OtrEncryptGhost`. -/
def OtrEncryptEnv (C : Crypto) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (uuidParse : UuidParser) (x : OtrEncryptGhost) (evs : List AllocEvent) : Prop :=
  OtrEncryptCoreEnv C S sendEnv uuidParse x.ot x.ptext x.loc x.rem x.rest evs

/-- Budget-threaded relocatable `[LibsignalPlacement]` specification of `OTR::encrypt`
    with arbitrary spatial frame `F` (`onOom = ⌜False⌝`, `allocFailedIn` dropped from `onPanic`). -/
def otrEncryptPlacedSpecF [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv) (F : SepProp) :
    Spec (OtrEncryptGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st (OtrEncryptEnv C S sendEnv uuidParse x)⌝ ∗
      (CryptoVerification.LibsignalTripleRatchet.Encrypt.otrEncryptPlacedSpecF
        C (A.atState lim st s) ctl uuidParse S F).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜OtrEncryptEnv C S sendEnv uuidParse x evs⌝ ∗
      (CryptoVerification.LibsignalTripleRatchet.Encrypt.otrEncryptPlacedSpecF
        C (A.atState lim (M.stepEvents evs st) sf) ctl uuidParse S F).post x s0 sf
  onPanic := fun (x, _) s0 sf =>
    ⌜((x.model C S uuidParse).1 = .error .panic ∨ S.sendPanics x.ot.pqrState x.rest) ∧
      s0.trace <+: sf.trace⌝ ∗
      anyHeap

/-- Budget-threaded relocatable `[LibsignalPlacement]` specification of `OTR::encrypt`
    (`onOom = ⌜False⌝`, `allocFailedIn` dropped from `onPanic`). -/
def otrEncryptPlacedSpec [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv) :
    Spec (OtrEncryptGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st (OtrEncryptEnv C S sendEnv uuidParse x)⌝ ∗
      (CryptoVerification.LibsignalTripleRatchet.Encrypt.otrEncryptPlacedSpec
        C (A.atState lim st s) ctl uuidParse S).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜OtrEncryptEnv C S sendEnv uuidParse x evs⌝ ∗
      (CryptoVerification.LibsignalTripleRatchet.Encrypt.otrEncryptPlacedSpec
        C (A.atState lim (M.stepEvents evs st) sf) ctl uuidParse S).post x s0 sf
  onPanic := fun (x, _) s0 sf =>
    ⌜((x.model C S uuidParse).1 = .error .panic ∨ S.sendPanics x.ot.pqrState x.rest) ∧
      s0.trace <+: sf.trace⌝ ∗
      anyHeap

theorem otrEncrypt_placed_ok_of_frame [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {uuidParse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    (h : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (otrEncryptPlacedSpecF C A lim ctl uuidParse S sendEnv emp))) :
    subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (otrEncryptPlacedSpec C A lim ctl uuidParse S sendEnv)) := by
  refine subroutine_ok_mono h ?_ ?_
  · rintro ⟨x, st⟩ R s0 hm
    simpa only [withLsCodeRoLoaded, otrEncryptPlacedSpecF, otrEncryptPlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.Encrypt.otrEncryptPlacedSpecF,
      CryptoVerification.LibsignalTripleRatchet.Encrypt.otrEncryptPlacedSpec, emp_sepConj] using hm
  · rintro ⟨x, st⟩ R s0 sf hm
    simpa only [withLsCodeRoLoaded, otrEncryptPlacedSpecF, otrEncryptPlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.Encrypt.otrEncryptPlacedSpecF,
      CryptoVerification.LibsignalTripleRatchet.Encrypt.otrEncryptPlacedSpec, emp_sepConj] using hm

/-! ## `PhaseCreditSpec` Helpers & Non-Vacuity Witnesses -/

theorem phaseCredit_eq_append {M : AllocCostModel} [HasFineReallocCredit M]
    {e₁ e₂ : List AllocEvent} {c₁ l₁ p₁ r₁ c₂ l₂ p₂ r₂ : Nat}
    (h₁ : PhaseCreditSpec M (· = e₁) c₁ l₁ p₁ r₁)
    (h₂ : PhaseCreditSpec M (· = e₂) c₂ l₂ p₂ r₂) :
    PhaseCreditSpec M (· = e₁ ++ e₂) (c₁ + c₂) (l₁ + l₂) (max p₁ (l₁ + p₂)) (max r₁ r₂) :=
  (h₁.concat h₂).of_imp fun _ h => ⟨e₁, e₂, h, rfl, rfl⟩

theorem phaseCredit_eq_append_sym {M : AllocCostModel} [HasFineReallocCredit M]
    {e₁ e₂ : List AllocEvent} {c₁ l₁ r₁ c₂ l₂ r₂ : Nat}
    (h₁ : PhaseCreditSpec M (· = e₁) c₁ l₁ l₁ r₁)
    (h₂ : PhaseCreditSpec M (· = e₂) c₂ l₂ l₂ r₂) :
    PhaseCreditSpec M (· = e₁ ++ e₂) (c₁ + c₂) (l₁ + l₂) (l₁ + l₂) (max r₁ r₂) :=
  (phaseCredit_eq_append h₁ h₂).mono (Nat.le_refl _) (Nat.le_refl _) (by omega) (Nat.le_refl _)

theorem phaseCredit_if_alloc {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (cond : Bool) (req al : Nat) (hal : al ≤ 16) :
    PhaseCreditSpec M (· = if cond = true then rustAllocEvents req al else [])
      (2 * req + 9539) (req + 8195) (req + 8195) req := by
  cases cond
  · simpa using (PhaseCreditSpec.nil M).mono (by omega) (by omega) (by omega) (by omega)
  · simpa using PhaseCreditSpec.rustAlloc_aff hM hal

theorem phaseCredit_if_dealloc {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (cond : Bool) (req al : Nat) :
    PhaseCreditSpec M (· = if cond = true then rustDeallocEvents req al else []) 0 0 0 0 := by
  cases cond
  · simpa using PhaseCreditSpec.nil M
  · simpa using PhaseCreditSpec.rustDealloc hM.freeNonInc req al

/-- Parametric `PhaseCreditSpec` for `SignalMessageNewEnv parse x` under `ModelHyps M`. -/
theorem signalMessageNewEnv_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (parse : UuidParser) (x : SignalMessageNewGhost) :
    let ctL := x.ciphertext.length
    let pqL := x.pqRatchet.length
    let serL := (encode (x.protoMsg parse)).length + 9
    PhaseCreditSpec M (SignalMessageNewEnv parse x)
      (4 * ctL + 4 * pqL + 2 * serL + 86121)
      (2 * ctL + 2 * pqL + serL + 73890)
      (2 * ctL + 2 * pqL + serL + 73890)
      (max (max 36 ctL) (max pqL serL)) := by
  dsimp only [SignalMessageNewEnv, signalMessageNewEvents, publicKeySerializeEvents,
    computeMacEvents]
  set ctL := x.ciphertext.length
  set pqL := x.pqRatchet.length
  set serL := (encode (x.protoMsg parse)).length + 9
  have h1 := phaseCredit_if_alloc hM (x.addresses parse).isSome 36 1 (by decide)
  have h2 := PhaseCreditSpec.rustAlloc_aff hM (req := 33) (al := 1) (by decide)
  have h3 : PhaseCreditSpec M (· = if x.ciphertext.isEmpty = true then [] else rustAllocEvents ctL 1)
      (2 * ctL + 9539) (ctL + 8195) (ctL + 8195) ctL := by
    cases x.ciphertext.isEmpty
    · simpa using PhaseCreditSpec.rustAlloc_aff hM (req := ctL) (al := 1) (by decide)
    · simpa using (PhaseCreditSpec.nil M).mono (by omega) (by omega) (by omega) (by omega)
  have h4 : PhaseCreditSpec M (· = if x.pqRatchet.isEmpty = true then [] else rustAllocEvents pqL 1)
      (2 * pqL + 9539) (pqL + 8195) (pqL + 8195) pqL := by
    cases x.pqRatchet.isEmpty
    · simpa using PhaseCreditSpec.rustAlloc_aff hM (req := pqL) (al := 1) (by decide)
    · simpa using (PhaseCreditSpec.nil M).mono (by omega) (by omega) (by omega) (by omega)
  have h5 := PhaseCreditSpec.rustAlloc_aff hM (req := serL) (al := 1) (by decide)
  have hd33 := PhaseCreditSpec.rustDealloc hM.freeNonInc 33 1
  have hmac1 := phaseCredit_eq_append_sym h2 hd33
  have hmac := phaseCredit_eq_append_sym hmac1 hmac1
  have hd_ct : PhaseCreditSpec M
      (· = if x.ciphertext.isEmpty = true then [] else rustDeallocEvents ctL 1) 0 0 0 0 := by
    cases x.ciphertext.isEmpty
    · simpa using PhaseCreditSpec.rustDealloc hM.freeNonInc ctL 1
    · simpa using PhaseCreditSpec.nil M
  have hd_pq : PhaseCreditSpec M
      (· = if x.pqRatchet.isEmpty = true then [] else rustDeallocEvents pqL 1) 0 0 0 0 := by
    cases x.pqRatchet.isEmpty
    · simpa using PhaseCreditSpec.rustDealloc hM.freeNonInc pqL 1
    · simpa using PhaseCreditSpec.nil M
  have hp :=
    phaseCredit_eq_append_sym
      (phaseCredit_eq_append_sym
        (phaseCredit_eq_append_sym
          (phaseCredit_eq_append_sym
            (phaseCredit_eq_append_sym
              (phaseCredit_eq_append_sym
                (phaseCredit_eq_append_sym
                  (phaseCredit_eq_append_sym
                    (phaseCredit_eq_append_sym (phaseCredit_eq_append_sym h1 h2) h3) h4) h5) hmac) h3) h4)
          hd33) hd_ct) hd_pq
  exact hp.mono (by omega) (by omega) (by omega) (by omega)

/-- Parametric `PhaseCreditSpec` for `OtrEncryptCoreEnv` when sizes are bounded by `bound`. -/
theorem otrEncryptCoreEnv_phaseCreditSpec_bounded {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (C : Crypto) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (uuidParse : UuidParser) (ot : OutgoingTripleRatchet (List (BitVec 8)))
    (ptext : List (BitVec 8)) (loc : Option AddrGhost) (rem : AddrGhost) (rest : List (BitVec 8))
    {cs ls ps rs : Nat} (bound : Nat)
    (hsend : PhaseCreditSpec M (sendEnv ot.pqrState rest) cs ls ps rs)
    (hpt : (ptext.length / 16 + 1) * 16 ≤ bound)
    (hsome : ∀ st' pqrKey pqrMsg, S.send ot.pqrState rest = some (st', pqrKey, pqrMsg) →
      let g := otrSignalMsgGhost C ot pqrKey pqrMsg ptext loc rem
      g.ciphertext.length ≤ bound ∧ g.pqRatchet.length ≤ bound ∧
        (encode (g.protoMsg uuidParse)).length + 9 ≤ bound) :
    PhaseCreditSpec M (OtrEncryptCoreEnv C S sendEnv uuidParse ot ptext loc rem rest)
      (cs + 12 * bound + 105263)
      (ls + 6 * bound + 90312)
      (max ps (ls + 6 * bound + 90312))
      (max rs (max 36 bound)) := by
  have hfr := PhaseCreditSpec.freeOnly_of_hyps hM
  have htail : PhaseCreditSpec M
      (fun evs' =>
        match S.send ot.pqrState rest with
        | none => FormatInnerEnv evs'
        | some (_, pqrKey, pqrMsg) =>
          SeqEnv (SeqEnv (· = rustAllocEvents 32 1) FreeOnlyEvs)
            (SeqEnv (· = rustAllocEvents ((ptext.length / 16 + 1) * 16) 1)
              (SeqEnv (SignalMessageNewEnv uuidParse (otrSignalMsgGhost C ot pqrKey pqrMsg ptext loc rem))
                FreeOnlyEvs)) evs')
      (12 * bound + 105263) (6 * bound + 90312) (6 * bound + 90312) (max 36 bound) := by
    cases hS : S.send ot.pqrState rest with
    | none =>
      dsimp only [FormatInnerEnv]
      exact (PhaseCreditSpec.nil M).mono (by omega) (by omega) (by omega) (by omega)
    | some val =>
      rcases val with ⟨st', pqrKey, pqrMsg⟩
      dsimp only
      obtain ⟨hct, hpqr, hser⟩ := hsome st' pqrKey pqrMsg hS
      have hmk := ((PhaseCreditSpec.rustAlloc_aff hM (req := 32) (al := 1) (by decide)).seq hfr)
      have haes := PhaseCreditSpec.rustAlloc_aff hM
        (req := (ptext.length / 16 + 1) * 16) (al := 1) (by decide)
      have hsm := (signalMessageNewEnv_phaseCreditSpec hM uuidParse
        (otrSignalMsgGhost C ot pqrKey pqrMsg ptext loc rem)).seq hfr
      exact (hmk.seq (haes.seq hsm)).mono (by omega) (by omega) (by omega) (by omega)
  exact (hsend.seq htail).mono (by omega) (by omega) (by omega) (by omega)

def witnessPublicKey : PublicKey := ⟨⟨List.replicate 32 0#8, by decide⟩⟩

def witnessPrivateKey : PrivateKey := ⟨⟨List.replicate 32 0#8, by decide⟩⟩

def witnessKeyPair : KeyPair := ⟨witnessPublicKey, witnessPrivateKey⟩

def witnessIdentityKey : IdentityKey := ⟨witnessPublicKey⟩

def witnessCrypto : Crypto where
  F := fun s _ => s
  E := fun _ b => b
  D := fun _ b => b
  X := fun _ _ => ⟨List.replicate 32 0#8, by decide⟩
  pubKey := fun _ => ⟨List.replicate 32 0#8, by decide⟩

/-- Concrete witness `SpqrModel` whose `send` returns `some ([1#8], none, [2#8])` (reaching the
    allocating `some` branch of `OtrEncryptCoreEnv` with non-empty `pqrMsg`). -/
def witnessSpqrModel : SpqrModel where
  send := fun _ _ => some ([1#8], none, [2#8])
  draws := fun _ _ => 0
  recv := fun _ _ => .ok ([], none)
  recvPanics := fun _ _ => false
  sendPanics := fun _ _ => false

/-- Concrete allocating `SpqrSendBudgetEnv` (`rustAllocEvents 16 1`). -/
def witnessSendEnv : SpqrSendBudgetEnv :=
  fun _ _ evs => evs = rustAllocEvents 16 1

def witnessUuidParse : UuidParser := fun _ => none

def witnessAddrGhost : AddrGhost :=
  ⟨⟨8#64, 8#64, [0x61#8]⟩, 1#8⟩

def witnessOtr : OutgoingTripleRatchet (List (BitVec 8)) where
  senderRatchetKey := witnessKeyPair
  senderChainKey := ⟨0#256, 0#32⟩
  previousCounter := 0#32
  pqrState := [1#8]
  sessionVersion := 4#8
  localIdentityKey := witnessIdentityKey
  remoteIdentityKey := witnessIdentityKey

/-- Concrete `OtrEncryptGhost` reaching the full allocating `some` path of `OtrEncryptEnv`. -/
def witnessOtrEncryptGhost : OtrEncryptGhost where
  ret := 0#64
  o := 0#64
  pqCap := 8#64
  pqPtr := 8#64
  ot := witnessOtr
  ptA := 0#64
  ptext := [0x41#8]
  locA := 0#64
  loc := none
  remA := 0#64
  rem := witnessAddrGhost
  cur := 0#64
  rest := [0x42#8]

/-- Inhabitation check: `OtrEncryptCoreEnv` on the witness arguments contains the full allocating
    trace (`sendEnv` `16` B + `32` B + `16` B AES + `<SignalMessage>::new`). -/
theorem otrEncryptCoreEnv_alloc_mem :
    let g := otrSignalMsgGhost witnessCrypto witnessOtr none [2#8] [0x41#8] none witnessAddrGhost
    OtrEncryptCoreEnv witnessCrypto witnessSpqrModel witnessSendEnv witnessUuidParse
      witnessOtr [0x41#8] none witnessAddrGhost [0x42#8]
      (rustAllocEvents 16 1 ++
        (rustAllocEvents 32 1 ++
          (rustAllocEvents 16 1 ++ signalMessageNewEvents witnessUuidParse g))) := by
  intro g
  refine Or.inr ⟨rustAllocEvents 16 1, _, rfl, rfl, ?_⟩
  dsimp only [witnessSpqrModel]
  refine Or.inr ⟨rustAllocEvents 32 1, _, rfl, Or.inl rfl, ?_⟩
  exact Or.inr ⟨rustAllocEvents 16 1, _, rfl, rfl, Or.inl rfl⟩

/-- Non-vacuity witness: `OtrEncryptCoreEnv` on the allocating `some` path satisfies
`FitsEnv fineCostModel` from `fineCostModel.init` under a `1 GiB` RAM budget. -/
theorem otrEncryptCoreEnv_fitsEnv_witness :
    FitsEnv fineCostModel
      { staticCount := 16, staticBytes := 16 * 1024 * 1024,
        physCap := 2 ^ 30, enforced := true }
      fineCostModel.init
      (OtrEncryptCoreEnv witnessCrypto witnessSpqrModel witnessSendEnv witnessUuidParse
        witnessOtr [0x41#8] none witnessAddrGhost [0x42#8]) := by
  have hsend := PhaseCreditSpec.rustAlloc_aff fineCostModel_modelHyps
    (req := 16) (al := 1) (by decide)
  have hSpec := otrEncryptCoreEnv_phaseCreditSpec_bounded fineCostModel_modelHyps
    witnessCrypto witnessSpqrModel witnessSendEnv witnessUuidParse
    witnessOtr [0x41#8] none witnessAddrGhost [0x42#8] 256 hsend (by decide)
    (fun st' pqrKey pqrMsg hS => by
      change some ([1#8], none, [2#8]) = some (st', pqrKey, pqrMsg) at hS
      injection hS with htuple
      injection htuple with h1 h23
      injection h23 with h2 h3
      subst h1 h2 h3
      exact ⟨by decide, by decide, by decide⟩)
  refine fitsEnv_fineCostModel_of_phaseCredit hSpec (by decide) rfl ?_ ?_
  · unfold fineStepReserveOfCum FineStepBound fineMaxMetaAreasOfCum pageAlignUp PAGE_SIZE
    decide
  · unfold fineStepReserveOfCum FineStepBound fineMaxMetaAreasOfCum fineDynIvsOfCum
      fineMaxGroupsOfCum pageAlignUp MMAP_MIN_ADDR PAGE_SIZE
    decide

/-- Non-vacuity witness for `OtrEncryptEnv` under `fineCostModel` and a `1 GiB` RAM budget. -/
theorem otrEncryptEnv_fitsEnv_witness :
    FitsEnv fineCostModel
      { staticCount := 16, staticBytes := 16 * 1024 * 1024,
        physCap := 2 ^ 30, enforced := true }
      fineCostModel.init
      (OtrEncryptEnv witnessCrypto witnessSpqrModel witnessSendEnv witnessUuidParse
        witnessOtrEncryptGhost) :=
  otrEncryptCoreEnv_fitsEnv_witness

end LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget

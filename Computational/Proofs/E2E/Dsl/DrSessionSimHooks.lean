/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.TablesHonest
public import Computational.Proofs.E2E.Dsl.ClampsLossless
public import Computational.Proofs.E2E.Dsl.SmReachInvParty
import Computational.Proofs.E2E.ComposedBinaryLinkV1

/-!
# SPQR DSL Hooks and Double Ratchet Helper Combinators

Defines the `SpqrDslHooks` interface between `SpqrSim` and `DrSessionSim`, `ghostPartsT` codecs
and accessors, bounded receiver-chain and skipped-key list combinators, and the `Comp.iter`
single-chain advance gadget `advanceSingleChainC`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.DrSessionSimHooks

open OracleSpec OracleComp
open ReductionDsl (Sig Ty Var Env Ops Samplers Iface Expr Comp iterM bits)
open CryptoGames (Party)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.Ratchet (keyToBytesVec32)
open CryptoGames.LibsignalSession (Crypto ShaCompress PublicKey PrivateKey KeyPair IdentityKey
  ChainKey MessageKeyGenerator SenderChain ReceiverChain RatchetState GhostState SessionState
  MessageType SignalProtocolError maxReceiverChains maxMessageKeys maxForwardJumps
  rootCreateChain liftE Mut)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal (TopStateTight)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.E2E (Bytes serializedPartyAddresses keyToBytes32_bytesToKey32)
open CryptoVerification.E2E.Costed (e2eSig B U8 U32 BV128 BV256 BV512 IdKey PK PlainT GhostStT
  drSenderChainT drRecvChainT ghostPartsT signalHdrT signalParsedT E2EPureOp E2ECryptoOp e2eOps
  ghostSplitEval ghostJoinEval partyToBool boolToParty)
open Computational.Proofs.E2E.Dsl.TablesHonest (e2ePureOp e2eCryptoOp eval_e2ePureOp
  cost_e2ePureOp eval_e2eCryptoOp cost_e2eCryptoOp)
open Computational.Proofs.E2E.Dsl.SmReachInvParty (serializedPartyAddresses_length_le_128)

/-! ## `SpqrDslHooks` interface -/

/-- Interface contract for SPQR V1 `send` and `recv` subprograms in `ReductionDsl` over `e2eOps`. -/
structure SpqrDslHooks (ℓ : ℕ) {Pt : Type} (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) where
  sendC : ∀ {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))},
    Expr (e2eOps ℓ P C K decT encT) Γ (.prod (B 32) BV512) →
    Comp (e2eOps ℓ P C K decT encT) I Γ (.opt (.prod (B 32) (.prod (.opt BV256) (B 32))))
  sendC_cost : ∀ {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ (.prod (B 32) BV512)),
    (sendC I e).cost ≤ e.cost + 65536
  sendC_queries : ∀ {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T)
    {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ (.prod (B 32) BV512))
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ),
    (sendC I e).queries w ws = 0
  sendC_eval : ∀ {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ (.prod (B 32) BV512)) (ρ : Env Γ),
    TopStateTight C.F K (e.eval ρ).1 →
    (sendC I e).eval ρ = pure (
      let (pq, r) := e.eval ρ
      let spqr := spqrV1SessionUniformCoins C.F K
      if spqr.sendPanics pq r then none
      else (spqr.send pq r).map fun (pq', saltVec?, pqMsg) =>
        (pq', (saltVec?.map (fun v => bytesToKey32 v.toList), pqMsg)))
  recvC : ∀ {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))},
    Expr (e2eOps ℓ P C K decT encT) Γ (.prod (B 32) (B 32)) →
    Comp (e2eOps ℓ P C K decT encT) I Γ (.opt (.prod (B 32) (.opt BV256)))
  recvC_cost : ∀ {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ (.prod (B 32) (B 32))),
    (recvC I e).cost ≤ e.cost + 4100000
  recvC_queries : ∀ {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T)
    {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ (.prod (B 32) (B 32)))
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ),
    (recvC I e).queries w ws = 0
  recvC_eval : ∀ {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ (.prod (B 32) (B 32))) (ρ : Env Γ),
    TopStateTight C.F K (e.eval ρ).1 →
    (recvC I e).eval ρ = pure (
      let (pq, pqMsg) := e.eval ρ
      let spqr := spqrV1SessionUniformCoins C.F K
      if spqr.recvPanics pq pqMsg then none
      else match spqr.recv pq pqMsg with
        | .ok (pq', saltVec?) =>
          some (pq', saltVec?.map (fun v => bytesToKey32 v.toList))
        | .error _ => none)

/-! ## Value codecs for `ghostPartsT` components -/

def encodeChainKey (ck : ChainKey) : BitVec 256 × BitVec 32 :=
  (ck.key, ck.index)

def decodeChainKey (p : BitVec 256 × BitVec 32) : ChainKey :=
  { key := p.1, index := p.2 }

@[simp] theorem decodeChainKey_encodeChainKey (ck : ChainKey) :
    decodeChainKey (encodeChainKey ck) = ck := by
  cases ck
  rfl

def encodeMsgKey (mk : MessageKeyGenerator) : BitVec 256 × BitVec 32 :=
  (bytesToKey32 mk.seed, mk.counter)

def decodeMsgKey (p : BitVec 256 × BitVec 32) : MessageKeyGenerator :=
  { seed := keyToBytes32 p.1, counter := p.2 }

theorem decodeMsgKey_encodeMsgKey {mk : MessageKeyGenerator} (h : mk.seed.length = 32) :
    decodeMsgKey (encodeMsgKey mk) = mk := by
  rcases mk with ⟨seed, ctr⟩
  dsimp only at h
  simp [encodeMsgKey, decodeMsgKey, keyToBytes32_bytesToKey32 seed h]

def encodeSenderChain {ℓ : ℕ} (sc : SenderChain) : (drSenderChainT (ℓ := ℓ)).denote :=
  ((sc.ratchetKey.publicKey, bytesToKey32 sc.ratchetKey.privateKey.bytes.toList),
   (sc.chainKey.key, sc.chainKey.index))

def decodeSenderChain {ℓ : ℕ} (p : (drSenderChainT (ℓ := ℓ)).denote) : SenderChain :=
  { ratchetKey := { publicKey := p.1.1, privateKey := ⟨keyToBytesVec32 p.1.2⟩ }
    chainKey := { key := p.2.1, index := p.2.2 } }

theorem keyVec_bytesToKey32_vec (v : List.Vector (BitVec 8) 32) :
    keyToBytesVec32 (bytesToKey32 v.toList) = v := by
  apply Subtype.ext
  exact keyToBytes32_bytesToKey32 v.toList v.toList_length

@[simp] theorem privateKey_roundtrip (pk : PrivateKey) :
    (⟨keyToBytesVec32 (bytesToKey32 pk.bytes.toList)⟩ : PrivateKey) = pk := by
  rcases pk with ⟨v⟩
  simp [keyVec_bytesToKey32_vec]

@[simp] theorem decodeSenderChain_encodeSenderChain {ℓ : ℕ} (sc : SenderChain) :
    decodeSenderChain (encodeSenderChain (ℓ := ℓ) sc) = sc := by
  rcases sc with ⟨⟨pub, priv⟩, ⟨ck, idx⟩⟩
  simp [encodeSenderChain, decodeSenderChain]

def encodeRecvChain {ℓ : ℕ} (rc : ReceiverChain) : (drRecvChainT (ℓ := ℓ)).denote :=
  (rc.senderRatchetKey,
   (rc.chainKey.map encodeChainKey, rc.messageKeys.map encodeMsgKey))

def decodeRecvChain {ℓ : ℕ} (p : (drRecvChainT (ℓ := ℓ)).denote) : ReceiverChain :=
  { senderRatchetKey := p.1
    chainKey := p.2.1.map decodeChainKey
    messageKeys := p.2.2.map decodeMsgKey }

theorem decodeMsgKeys_encodeMsgKeys :
    ∀ (mks : List MessageKeyGenerator),
      (∀ mk ∈ mks, mk.seed.length = 32) →
      (mks.map encodeMsgKey).map decodeMsgKey = mks
  | [], _ => rfl
  | mk :: rest, hmk => by
    have h0 := hmk mk List.mem_cons_self
    have htail := decodeMsgKeys_encodeMsgKeys rest (fun x hx => hmk x (List.mem_cons_of_mem _ hx))
    simp [decodeMsgKey_encodeMsgKey h0, htail]

theorem decodeRecvChain_encodeRecvChain {ℓ : ℕ} {rc : ReceiverChain}
    (hmk : ∀ mk ∈ rc.messageKeys, mk.seed.length = 32) :
    decodeRecvChain (encodeRecvChain (ℓ := ℓ) rc) = rc := by
  rcases rc with ⟨srk, ck?, mks⟩
  simp only [encodeRecvChain, decodeRecvChain, decodeMsgKeys_encodeMsgKeys mks hmk,
    ReceiverChain.mk.injEq, true_and, and_true]
  cases ck? <;> simp

theorem decodeRecvChains_encodeRecvChains {ℓ : ℕ} :
    ∀ (rcs : List ReceiverChain),
      (∀ rc ∈ rcs, ∀ mk ∈ rc.messageKeys, mk.seed.length = 32) →
      (rcs.map (encodeRecvChain (ℓ := ℓ))).map decodeRecvChain = rcs
  | [], _ => rfl
  | rc :: rest, hrc => by
    have h0 := hrc rc List.mem_cons_self
    have htail := decodeRecvChains_encodeRecvChains (ℓ := ℓ) rest
      (fun x hx => hrc x (List.mem_cons_of_mem _ hx))
    simp [decodeRecvChain_encodeRecvChain h0, htail]

@[simp] theorem salt_roundtrip (s? : Option (List.Vector (BitVec 8) 32)) :
    (s?.map (fun v => bytesToKey32 v.toList)).map keyToBytesVec32 = s? := by
  cases s? with
  | none => rfl
  | some v => simp [keyVec_bytesToKey32_vec]

@[simp] theorem boolToParty_partyToBool_eq (p : Party) :
    boolToParty (partyToBool p) = p := by
  cases p <;> rfl

theorem chainKey_messageKeys_seed_len (F : ShaCompress) (ck : ChainKey) :
    (ck.messageKeys F).seed.length = 32 := by
  simp [ChainKey.messageKeys, CryptoGames.Ratchet.chainHmac,
    CryptoVerification.LibsignalSpqrV1.length_hmacWith]

theorem ghostSplitEval_eq_of_le {ℓ : ℕ} {g : GhostState Bytes}
    (hrc : g.session.receiverChains.length ≤ 5) :
    ghostSplitEval (ℓ := ℓ) g =
      (partyToBool g.party,
       (g.session.sessionVersion,
        (g.session.localIdentity,
         (g.session.remoteIdentity,
          (g.session.rootKey,
           (g.session.previousCounter,
            (g.session.pendingPreKey,
             (g.epoch,
              (g.chainEpochs,
               (g.session.senderChain.map (encodeSenderChain (ℓ := ℓ)),
                (g.session.receiverChains.map (encodeRecvChain (ℓ := ℓ)),
                 g.session.pqRatchetState))))))))))) := by
  unfold ghostSplitEval
  simp only [List.take_of_length_le hrc]
  rfl

theorem ghostJoinEval_eq_of_le {ℓ : ℕ}
    (isB : Bool) (ver : BitVec 32) (locId : IdentityKey) (remId? : Option IdentityKey)
    (rk : BitVec 256) (prevCtr : BitVec 32) (pend : Bool) (ep : ℕ) (cEps : List ℕ)
    (sc? : Option (drSenderChainT (ℓ := ℓ)).denote)
    (rcs : List (drRecvChainT (ℓ := ℓ)).denote) (pqSt : Bytes)
    (hrc : rcs.length ≤ 5) :
    ghostJoinEval (ℓ := ℓ)
        (isB, (ver, (locId, (remId?, (rk, (prevCtr, (pend, (ep, (cEps, (sc?, (rcs, pqSt))))))))))) =
      { party := boolToParty isB
        session :=
          { sessionVersion := ver
            localIdentity := locId
            remoteIdentity := remId?
            rootKey := rk
            previousCounter := prevCtr
            senderChain := sc?.map decodeSenderChain
            receiverChains := rcs.map decodeRecvChain
            pendingPreKey := pend
            pqRatchetState := pqSt }
        epoch := ep
        chainEpochs := cEps } := by
  unfold ghostJoinEval
  simp only [List.take_of_length_le hrc]
  rfl

/-! ## `ghostPartsT` accessors and `Expr` helpers -/

section ExprCombinators

variable {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

local notation "S" => e2eSig ℓ
local notation "OO" => e2eOps ℓ P C K decT encT

def gpIsB {O' : Ops S} {Γ} (p : Expr O' Γ ghostPartsT) : Expr O' Γ .bool := .fst p
def gpVer {O' : Ops S} {Γ} (p : Expr O' Γ ghostPartsT) : Expr O' Γ U32 := .fst (.snd p)
def gpLocId {O' : Ops S} {Γ} (p : Expr O' Γ ghostPartsT) : Expr O' Γ IdKey :=
  .fst (.snd (.snd p))
def gpRemId {O' : Ops S} {Γ} (p : Expr O' Γ ghostPartsT) : Expr O' Γ (.opt IdKey) :=
  .fst (.snd (.snd (.snd p)))
def gpRk {O' : Ops S} {Γ} (p : Expr O' Γ ghostPartsT) : Expr O' Γ BV256 :=
  .fst (.snd (.snd (.snd (.snd p))))
def gpPrevCtr {O' : Ops S} {Γ} (p : Expr O' Γ ghostPartsT) : Expr O' Γ U32 :=
  .fst (.snd (.snd (.snd (.snd (.snd p)))))
def gpPend {O' : Ops S} {Γ} (p : Expr O' Γ ghostPartsT) : Expr O' Γ .bool :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd p))))))
def gpEp {O' : Ops S} {Γ} (p : Expr O' Γ ghostPartsT) : Expr O' Γ .nat :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd p)))))))
def gpCEps {O' : Ops S} {Γ} (p : Expr O' Γ ghostPartsT) : Expr O' Γ (.list .nat) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd p))))))))
def gpSc {O' : Ops S} {Γ} (p : Expr O' Γ ghostPartsT) : Expr O' Γ (.opt drSenderChainT) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd p)))))))))
def gpRcs {O' : Ops S} {Γ} (p : Expr O' Γ ghostPartsT) : Expr O' Γ (.list drRecvChainT) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd p))))))))))
def gpPqSt {O' : Ops S} {Γ} (p : Expr O' Γ ghostPartsT) : Expr O' Γ (B 32) :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd p))))))))))

def gpMk {O' : Ops S} {Γ}
    (isB : Expr O' Γ .bool)
    (ver : Expr O' Γ U32)
    (locId : Expr O' Γ IdKey)
    (remId? : Expr O' Γ (.opt IdKey))
    (rk : Expr O' Γ BV256)
    (prevCtr : Expr O' Γ U32)
    (pend : Expr O' Γ .bool)
    (ep : Expr O' Γ .nat)
    (cEps : Expr O' Γ (.list .nat))
    (sc? : Expr O' Γ (.opt drSenderChainT))
    (rcs : Expr O' Γ (.list drRecvChainT))
    (pqSt : Expr O' Γ (B 32)) : Expr O' Γ ghostPartsT :=
  .pair isB (.pair ver (.pair locId (.pair remId? (.pair rk (.pair prevCtr
    (.pair pend (.pair ep (.pair cEps (.pair sc? (.pair rcs pqSt))))))))))

def optBytes32LitE {Γ} : Option Bytes → Expr OO Γ (.opt (B 32))
  | none => .none
  | some bs => .some (e2ePureOp (.bytesLit 32 bs) .unit)

@[simp] theorem eval_optBytes32LitE {Γ} (opt : Option Bytes) (ρ : Env Γ) :
    (optBytes32LitE (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      opt).eval ρ = opt := by
  cases opt <;> rfl

theorem cost_optBytes32LitE_le {Γ : List (Ty S)} (opt : Option Bytes)
    (h : ∀ bs ∈ opt, bs.length ≤ 128) :
    (optBytes32LitE (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      (Γ := Γ) opt).cost ≤ 162 := by
  cases opt with
  | none =>
    simp only [optBytes32LitE, Expr.cost]
    omega
  | some bs =>
    have hbs := h bs rfl
    have h32 : ((32 : ℕ+) : ℕ) = 32 := rfl
    simp only [optBytes32LitE, Expr.cost, cost_e2ePureOp, E2EPureOp.cost, h32]
    omega

def sendAddrsE {Γ} (isB : Expr OO Γ .bool) : Expr OO Γ (.opt (B 32)) :=
  .ite isB
    (optBytes32LitE (serializedPartyAddresses uuidTryParse .B .A))
    (optBytes32LitE (serializedPartyAddresses uuidTryParse .A .B))

theorem eval_sendAddrsE {Γ} (isB : Expr OO Γ .bool) (ρ : Env Γ) :
    (sendAddrsE (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT) isB).eval ρ =
      match boolToParty (isB.eval ρ) with
      | .A => serializedPartyAddresses uuidTryParse .A .B
      | .B => serializedPartyAddresses uuidTryParse .B .A := by
  dsimp only [sendAddrsE, Expr.eval]
  cases isB.eval ρ <;> simp [boolToParty]

theorem cost_sendAddrsE_le {Γ} (isB : Expr OO Γ .bool) :
    (sendAddrsE (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT) isB).cost ≤
      isB.cost + 163 := by
  dsimp only [sendAddrsE, Expr.cost]
  have hAB := cost_optBytes32LitE_le (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Γ)
    (serializedPartyAddresses uuidTryParse .A .B)
    (serializedPartyAddresses_length_le_128 uuidTryParse .A .B)
  have hBA := cost_optBytes32LitE_le (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Γ)
    (serializedPartyAddresses uuidTryParse .B .A)
    (serializedPartyAddresses_length_le_128 uuidTryParse .B .A)
  omega

def expectedAddrsE {Γ} (isB : Expr OO Γ .bool) : Expr OO Γ (.opt (B 32)) :=
  .ite isB
    (optBytes32LitE (serializedPartyAddresses uuidTryParse .A .B))
    (optBytes32LitE (serializedPartyAddresses uuidTryParse .B .A))

theorem eval_expectedAddrsE {Γ} (isB : Expr OO Γ .bool) (ρ : Env Γ) :
    (expectedAddrsE (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      isB).eval ρ =
      match boolToParty (isB.eval ρ) with
      | .A => serializedPartyAddresses uuidTryParse .B .A
      | .B => serializedPartyAddresses uuidTryParse .A .B := by
  dsimp only [expectedAddrsE, Expr.eval]
  cases isB.eval ρ <;> simp [boolToParty]

theorem cost_expectedAddrsE_le {Γ} (isB : Expr OO Γ .bool) :
    (expectedAddrsE (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      isB).cost ≤ isB.cost + 163 := by
  dsimp only [expectedAddrsE, Expr.cost]
  have hAB := cost_optBytes32LitE_le (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Γ)
    (serializedPartyAddresses uuidTryParse .A .B)
    (serializedPartyAddresses_length_le_128 uuidTryParse .A .B)
  have hBA := cost_optBytes32LitE_le (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Γ)
    (serializedPartyAddresses uuidTryParse .B .A)
    (serializedPartyAddresses_length_le_128 uuidTryParse .B .A)
  omega

def sessionVersionEffE {Γ} (ver : Expr OO Γ U32) : Expr OO Γ U32 :=
  .letE ver
    (.ite (e2ePureOp .u32Eq (.pair .v0 (e2ePureOp (.u32Lit 0#32) .unit)))
      (e2ePureOp (.u32Lit 2#32) .unit)
      .v0)

@[simp] theorem eval_sessionVersionEffE {Γ} (ver : Expr OO Γ U32) (ρ : Env Γ) :
    (sessionVersionEffE ver).eval ρ = if ver.eval ρ = 0 then 2 else ver.eval ρ := by
  dsimp only [sessionVersionEffE, Expr.eval, eval_e2ePureOp, E2EPureOp.eval, Expr.v0, Env.get]
  simp only [beq_iff_eq]
  rfl

@[simp] theorem cost_sessionVersionEffE {Γ} (ver : Expr OO Γ U32) :
    (sessionVersionEffE (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      ver).cost = ver.cost + 9 := by
  simp only [sessionVersionEffE, Expr.cost, Expr.v0, cost_e2ePureOp, E2EPureOp.cost]
  omega

/-! ## Bounded list combinators -/

private def drop1Step {α : Type} (x : α) (acc : List α × List α) : List α × List α :=
  (x :: acc.1, acc.1)

private theorem foldr_drop1Step_fst {α : Type} :
    ∀ (l : List α), (l.foldr drop1Step ([], [])).1 = l
  | [] => rfl
  | x :: xs => by
    simp [List.foldr_cons, drop1Step, foldr_drop1Step_fst xs]

private theorem foldr_drop1Step_snd {α : Type} :
    ∀ (l : List α), (l.foldr drop1Step ([], [])).2 = l.drop 1
  | [] => rfl
  | _ :: xs => by
    simp [List.foldr_cons, drop1Step, foldr_drop1Step_fst xs]

def drop1BE {O' : Ops S} {Γ t} (cap : ℕ) (xs : Expr O' Γ (.list t)) : Expr O' Γ (.list t) :=
  .snd (.foldrB cap xs (.pair .nil .nil) (.pair (.cons .v0 (.fst .v1)) (.fst .v1)))

theorem eval_drop1BE {O' : Ops S} {Γ t} (cap : ℕ) (xs : Expr O' Γ (.list t)) (ρ : Env Γ)
    (hlen : (xs.eval ρ).length ≤ cap) :
    (drop1BE cap xs).eval ρ = (xs.eval ρ).drop 1 := by
  simp only [drop1BE, Expr.eval, Expr.v0, Expr.v1, Env.get]
  rw [List.take_of_length_le hlen]
  exact foldr_drop1Step_snd (xs.eval ρ)

def pushEvict5E {O' : Ops S} {Γ t} (xs : Expr O' Γ (.list t)) (x : Expr O' Γ t) :
    Expr O' Γ (.list t) :=
  .letE (.pair xs x)
    (let xs0 : Expr O' _ (.list t) := .fst .v0
     let x0 : Expr O' _ t := .snd .v0
     let base : Expr O' _ (.list t) := .ite (.lt (.len xs0) (.nat 5)) xs0 (drop1BE 5 xs0)
     .appendL 5 base (.cons x0 .nil))

theorem eval_pushEvict5E {O' : Ops S} {Γ t} (xs : Expr O' Γ (.list t)) (x : Expr O' Γ t)
    (ρ : Env Γ) (hlen : (xs.eval ρ).length ≤ 5) :
    (pushEvict5E xs x).eval ρ =
      (xs.eval ρ ++ [x.eval ρ]).drop (((xs.eval ρ).length + 1) - 5) := by
  simp only [pushEvict5E, Expr.eval, Expr.v0, Env.get, decide_eq_true_eq]
  rw [eval_drop1BE 5 (Expr.var Var.zero).fst (Env.cons (xs.eval ρ, x.eval ρ) ρ)
    (by simpa [Expr.eval, Env.get] using hlen)]
  by_cases hlt5 : (xs.eval ρ).length < 5
  · have hsub : ((xs.eval ρ).length + 1) - 5 = 0 := by omega
    simp only [hlt5, hsub, ↓reduceIte, List.drop]
    exact List.take_of_length_le (by simp; omega)
  · have h5 : (xs.eval ρ).length = 5 := by omega
    have hsub : ((xs.eval ρ).length + 1) - 5 = 1 := by omega
    simp only [hlt5, hsub, ↓reduceIte]
    rcases hxs : xs.eval ρ with _ | ⟨a, tl⟩
    · simp [hxs] at h5
    · simp only [hxs, List.length_cons] at h5
      have htake : (tl ++ [x.eval ρ]).take 5 = tl ++ [x.eval ρ] :=
        List.take_of_length_le (by simp; omega)
      simpa [Expr.eval, Env.get, List.drop] using htake

private def getLastBoolStep (x : ℕ) (acc : Bool × ℕ) : Bool × ℕ :=
  if acc.1 then acc else (true, x)

private theorem foldr_getLastBoolStep :
    ∀ (l : List ℕ),
      match l.getLast? with
      | none => l.foldr getLastBoolStep (false, 0) = (false, 0)
      | some z => l.foldr getLastBoolStep (false, 0) = (true, z)
  | [] => rfl
  | [a] => rfl
  | a :: b :: rest => by
    have ih := foldr_getLastBoolStep (b :: rest)
    have hne : b :: rest ≠ [] := List.cons_ne_nil b rest
    rcases Option.isSome_iff_exists.mp (List.getLast?_isSome.mpr hne) with ⟨z, hz⟩
    rw [hz] at ih
    simp [List.foldr_cons, getLastBoolStep, List.getLast?_cons_cons, hz, ih]

private theorem getLast?_take_succ :
    ∀ (l : List ℕ) (i : ℕ), i < l.length → (l.take (i + 1)).getLast? = some (l.getD i 0)
  | [], _, hi => nomatch hi
  | a :: _, 0, _ => rfl
  | _ :: b :: tl, i + 1, hi => by
    have hi' : i < (b :: tl).length := by
      simp only [List.length_cons] at hi ⊢
      omega
    have ih := getLast?_take_succ (b :: tl) i hi'
    simpa [List.take_succ_cons, List.getLast?_cons_cons, List.getD] using ih

def getDZero5E {O' : Ops S} {Γ} (cEps : Expr O' Γ (.list .nat)) (idx : Expr O' Γ .nat) :
    Expr O' Γ .nat :=
  .letE (.pair cEps idx)
    (let l0 : Expr O' _ (.list .nat) := .fst .v0
     let i0 : Expr O' _ .nat := .snd .v0
     .ite (.lt i0 (.len l0))
       (.snd
         (.foldrB 5 (.take (.add i0 (.nat 1)) l0) (.pair (.bool false) (.nat 0))
           (.ite (.fst .v1) .v1 (.pair (.bool true) .v0))))
       (.nat 0))

theorem eval_getDZero5E {O' : Ops S} {Γ} (cEps : Expr O' Γ (.list .nat)) (idx : Expr O' Γ .nat)
    (ρ : Env Γ) (hlen : (cEps.eval ρ).length ≤ 5) :
    (getDZero5E cEps idx).eval ρ = (cEps.eval ρ).getD (idx.eval ρ) 0 := by
  simp only [getDZero5E, Expr.eval, Expr.v0, Expr.v1, Env.get, decide_eq_true_eq]
  by_cases hlt : idx.eval ρ < (cEps.eval ρ).length
  · simp only [hlt, ↓reduceIte]
    have htake5 : ((cEps.eval ρ).take (idx.eval ρ + 1)).take 5 =
        (cEps.eval ρ).take (idx.eval ρ + 1) :=
      List.take_of_length_le (Nat.le_trans (List.length_take_le' _ _) hlen)
    rw [htake5]
    have hlast := foldr_getLastBoolStep ((cEps.eval ρ).take (idx.eval ρ + 1))
    rw [getLast?_take_succ (cEps.eval ρ) (idx.eval ρ) hlt] at hlast
    exact congrArg Prod.snd hlast
  · simp only [hlt, ↓reduceIte]
    have hge : (cEps.eval ρ).length ≤ idx.eval ρ := Nat.le_of_not_lt hlt
    simp [List.getD, List.getElem?_eq_none hge]

private def findWithIdxStep {α : Type} (p : α → Bool) (x : α) (acc : ℕ × Option α) :
    ℕ × Option α :=
  if p x then (0, some x) else (acc.1 + 1, acc.2)

private theorem foldr_findWithIdxStep {α : Type} (p : α → Bool) :
    ∀ (l : List α),
      match l.findIdx? p with
      | none => (l.foldr (findWithIdxStep p) (0, none)).2 = none
      | some i => (l.foldr (findWithIdxStep p) (0, none)) = (i, l[i]?)
  | [] => rfl
  | x :: xs => by
    have ih := foldr_findWithIdxStep p xs
    simp only [List.findIdx?_cons, List.foldr_cons, findWithIdxStep]
    cases hp : p x
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases hf : xs.findIdx? p with
      | none =>
        rw [hf] at ih
        simp [ih]
      | some j =>
        rw [hf] at ih
        simp [ih]
    · simp

def findChainWithIdx5E {Γ} (rcs : Expr OO Γ (.list drRecvChainT)) (their : Expr OO Γ PK) :
    Expr OO Γ (.prod .nat (.opt drRecvChainT)) :=
  .letE (.pair rcs their)
    (.foldrB 5 (.fst .v0) (.pair (.nat 0) .none)
      (.ite (e2ePureOp .pkEq (.pair (.fst .v0) (.snd .v2)))
        (.pair (.nat 0) (.some .v0))
        (.pair (.add (.fst .v1) (.nat 1)) (.snd .v1))))

theorem eval_findChainWithIdx5E {Γ} (rcs : Expr OO Γ (.list drRecvChainT))
    (their : Expr OO Γ PK) (ρ : Env Γ) (hlen : (rcs.eval ρ).length ≤ 5) :
    match (rcs.eval ρ).findIdx? (fun c => c.1 == their.eval ρ) with
    | none => ((findChainWithIdx5E rcs their).eval ρ).2 = none
    | some i => (findChainWithIdx5E rcs their).eval ρ = (i, (rcs.eval ρ)[i]?) := by
  simp only [findChainWithIdx5E, Expr.eval, eval_e2ePureOp, E2EPureOp.eval,
    Expr.v0, Expr.v1, Expr.v2, Env.get]
  rw [List.take_of_length_le hlen]
  exact foldr_findWithIdxStep (fun c => c.1 == their.eval ρ) (rcs.eval ρ)

private def replaceFirstStep {α : Type} (p : α → Bool) (newVal : α) (x : α)
    (acc : List α × List α) : List α × List α :=
  (x :: acc.1, if p x then newVal :: acc.1 else x :: acc.2)

private theorem foldr_replaceFirstStep_fst {α : Type} (p : α → Bool) (newVal : α) :
    ∀ (l : List α), (l.foldr (replaceFirstStep p newVal) ([], [])).1 = l
  | [] => rfl
  | x :: xs => by
    simp [List.foldr_cons, replaceFirstStep, foldr_replaceFirstStep_fst p newVal xs]

private theorem foldr_replaceFirstStep_snd {α : Type} (p : α → Bool) (newVal : α) :
    ∀ (l : List α) {i : ℕ}, l.findIdx? p = some i →
      (l.foldr (replaceFirstStep p newVal) ([], [])).2 = l.set i newVal
  | [], _, h => nomatch h
  | x :: xs, i, h => by
    simp only [List.findIdx?_cons] at h
    simp only [List.foldr_cons, replaceFirstStep, foldr_replaceFirstStep_fst p newVal xs]
    cases hp : p x
    · rw [hp] at h
      rcases Option.mem_map.mp h with ⟨j, hj, rfl⟩
      simp [Bool.false_eq_true, List.set_cons_succ, foldr_replaceFirstStep_snd p newVal xs hj]
    · rw [hp] at h
      injection h with hi
      subst hi
      simp

def replaceFirstChain5E {Γ} (rcs : Expr OO Γ (.list drRecvChainT)) (their : Expr OO Γ PK)
    (newRc : Expr OO Γ drRecvChainT) : Expr OO Γ (.list drRecvChainT) :=
  .letE (.pair rcs (.pair their newRc))
    (.snd
      (.foldrB 5 (.fst .v0) (.pair .nil .nil)
        (let elem : Expr OO _ drRecvChainT := .v0
         let acc : Expr OO _ (.prod (.list drRecvChainT) (.list drRecvChainT)) := .v1
         let th : Expr OO _ PK := .fst (.snd .v2)
         let rep : Expr OO _ drRecvChainT := .snd (.snd .v2)
         .pair (.cons elem (.fst acc))
           (.ite (e2ePureOp .pkEq (.pair (.fst elem) th))
             (.cons rep (.fst acc))
             (.cons elem (.snd acc))))))

theorem eval_replaceFirstChain5E {Γ} (rcs : Expr OO Γ (.list drRecvChainT))
    (their : Expr OO Γ PK) (newRc : Expr OO Γ drRecvChainT) (ρ : Env Γ)
    (hlen : (rcs.eval ρ).length ≤ 5)
    {i : ℕ} (hidx : (rcs.eval ρ).findIdx? (fun c => c.1 == their.eval ρ) = some i) :
    (replaceFirstChain5E rcs their newRc).eval ρ = (rcs.eval ρ).set i (newRc.eval ρ) := by
  simp only [replaceFirstChain5E, Expr.eval, eval_e2ePureOp, E2EPureOp.eval,
    Expr.v0, Expr.v1, Expr.v2, Env.get]
  rw [List.take_of_length_le hlen]
  exact foldr_replaceFirstStep_snd (fun c => c.1 == their.eval ρ) (newRc.eval ρ) (rcs.eval ρ) hidx

private def takeFirstMatchStep {α : Type} (p : α → Bool) (x : α)
    (acc : Option α × List α × List α) : Option α × List α × List α :=
  if p x then (some x, x :: acc.2.1, acc.2.1)
  else (acc.1, x :: acc.2.1, x :: acc.2.2)

private theorem foldr_takeFirstMatchStep_all {α : Type} (p : α → Bool) :
    ∀ (l : List α), (l.foldr (takeFirstMatchStep p) (none, [], [])).2.1 = l
  | [] => rfl
  | x :: xs => by
    dsimp only [List.foldr_cons, takeFirstMatchStep]
    rw [foldr_takeFirstMatchStep_all p xs]
    split <;> rfl

private theorem foldr_takeFirstMatchStep {α : Type} (p : α → Bool) :
    ∀ (l : List α),
      match l.findIdx? p with
      | none =>
        (l.foldr (takeFirstMatchStep p) (none, [], [])).1 = none ∧
        (l.foldr (takeFirstMatchStep p) (none, [], [])).2.2 = l
      | some pos =>
        (l.foldr (takeFirstMatchStep p) (none, [], [])).1 = l[pos]? ∧
        (l.foldr (takeFirstMatchStep p) (none, [], [])).2.2 = l.eraseIdx pos
  | [] => ⟨rfl, rfl⟩
  | x :: xs => by
    have ih := foldr_takeFirstMatchStep p xs
    simp only [List.findIdx?_cons, List.foldr_cons, takeFirstMatchStep,
      foldr_takeFirstMatchStep_all p xs]
    cases hp : p x
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases hf : xs.findIdx? p with
      | none =>
        rw [hf] at ih
        exact ⟨ih.1, congrArg (x :: ·) ih.2⟩
      | some j =>
        rw [hf] at ih
        refine ⟨?_, ?_⟩
        · simpa using ih.1
        · simp [List.eraseIdx_cons_succ, ih.2]
    · simp

def takeSkippedFromListE {Γ} (mks : Expr OO Γ (.list (.prod BV256 U32)))
    (targetCtr : Expr OO Γ U32) :
    Expr OO Γ (.prod (.opt (.prod BV256 U32)) (.list (.prod BV256 U32))) :=
  .letE (.pair mks targetCtr)
    (let r : Expr OO _
        (.prod (.opt (.prod BV256 U32))
          (.prod (.list (.prod BV256 U32)) (.list (.prod BV256 U32)))) :=
      .foldrB 2000 (.fst .v0) (.pair .none (.pair .nil .nil))
        (let elem : Expr OO _ (.prod BV256 U32) := .v0
         let acc : Expr OO _
           (.prod (.opt (.prod BV256 U32))
             (.prod (.list (.prod BV256 U32)) (.list (.prod BV256 U32)))) := .v1
         let ctr : Expr OO _ U32 := .snd .v2
         .ite (e2ePureOp .u32Eq (.pair (.snd elem) ctr))
           (.pair (.some elem) (.pair (.cons elem (.fst (.snd acc))) (.fst (.snd acc))))
           (.pair (.fst acc)
             (.pair (.cons elem (.fst (.snd acc))) (.cons elem (.snd (.snd acc))))))
     .letE r (.pair (.fst .v0) (.snd (.snd .v0))))

theorem eval_takeSkippedFromListE {Γ} (mks : Expr OO Γ (.list (.prod BV256 U32)))
    (targetCtr : Expr OO Γ U32) (ρ : Env Γ) (hlen : (mks.eval ρ).length ≤ 2000) :
    match (mks.eval ρ).findIdx? (fun mk => mk.2 == targetCtr.eval ρ) with
    | none => (takeSkippedFromListE mks targetCtr).eval ρ = (none, mks.eval ρ)
    | some pos =>
      (takeSkippedFromListE mks targetCtr).eval ρ =
        ((mks.eval ρ)[pos]?, (mks.eval ρ).eraseIdx pos) := by
  simp only [takeSkippedFromListE, Expr.eval, eval_e2ePureOp, E2EPureOp.eval,
    Expr.v0, Expr.v1, Expr.v2, Env.get]
  rw [List.take_of_length_le hlen]
  have h := foldr_takeFirstMatchStep (fun mk : BitVec 256 × BitVec 32 => mk.2 == targetCtr.eval ρ)
    (mks.eval ρ)
  cases hf : (mks.eval ρ).findIdx? (fun mk => mk.2 == targetCtr.eval ρ) with
  | none =>
    rw [hf] at h
    exact Prod.ext h.1 h.2
  | some pos =>
    rw [hf] at h
    exact Prod.ext h.1 h.2

theorem cost_pushEvict5E_le {O' : Ops S} {Γ t} (xs : Expr O' Γ (.list t)) (x : Expr O' Γ t) :
    (pushEvict5E xs x).cost ≤ xs.cost + x.cost + 90 := by
  simp only [pushEvict5E, drop1BE, Expr.cost, Expr.v0, Expr.v1]
  have hb : bits 5 = 3 := by decide
  rw [hb]
  omega

theorem cost_getDZero5E_le {O' : Ops S} {Γ} (cEps : Expr O' Γ (.list .nat))
    (idx : Expr O' Γ .nat) :
    (getDZero5E cEps idx).cost ≤ cEps.cost + idx.cost + 60 := by
  simp only [getDZero5E, Expr.cost, Expr.v0, Expr.v1]
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  rw [hb0, hb1]
  omega

theorem cost_findChainWithIdx5E_le {Γ} (rcs : Expr OO Γ (.list drRecvChainT))
    (their : Expr OO Γ PK) :
    (findChainWithIdx5E (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      rcs their).cost ≤ rcs.cost + their.cost + 120 := by
  simp only [findChainWithIdx5E, Expr.cost, Expr.v0, Expr.v1, Expr.v2, cost_e2ePureOp,
    E2EPureOp.cost]
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  rw [hb0, hb1]
  omega

theorem cost_replaceFirstChain5E_le {Γ} (rcs : Expr OO Γ (.list drRecvChainT))
    (their : Expr OO Γ PK) (newRc : Expr OO Γ drRecvChainT) :
    (replaceFirstChain5E (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      rcs their newRc).cost ≤ rcs.cost + their.cost + newRc.cost + 150 := by
  simp only [replaceFirstChain5E, Expr.cost, Expr.v0, Expr.v1, Expr.v2, cost_e2ePureOp,
    E2EPureOp.cost]
  omega

theorem cost_takeSkippedFromListE_le {Γ} (mks : Expr OO Γ (.list (.prod BV256 U32)))
    (targetCtr : Expr OO Γ U32) :
    (takeSkippedFromListE (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      mks targetCtr).cost ≤ mks.cost + targetCtr.cost + 44020 := by
  simp only [takeSkippedFromListE, Expr.cost, Expr.v0, Expr.v1, Expr.v2, cost_e2ePureOp,
    E2EPureOp.cost]
  omega

/-! ## Bounded single-chain advance -/

@[reducible] def chainAdvAccT (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .opt (.prod (.prod BV256 U32) (.list (.prod BV256 U32)))

def chainAdvStepFn (F : ShaCompress) (targetCtr : BitVec 32) :
    Option ((BitVec 256 × BitVec 32) × List (BitVec 256 × BitVec 32)) →
    Option ((BitVec 256 × BitVec 32) × List (BitVec 256 × BitVec 32))
  | none => none
  | some ((ck, idx), mks) =>
    if idx < targetCtr then
      let ckObj : ChainKey := { key := ck, index := idx }
      match ckObj.nextChainKey F with
      | .ok ckNext =>
        let mkSeed := bytesToKey32 (ckObj.messageKeys F).seed
        some ((ckNext.key, ckNext.index), ((mkSeed, idx) :: mks).take 2000)
      | .error _ => none
    else
      some ((ck, idx), mks)

/-- Advances `(ck, mks)` up to `targetCtr` in `25,000` bounded `Comp.iter` steps. -/
def advanceSingleChainC {ι : Type} {T : OracleSpec ι} (I : Iface S T) {Γ}
    (ckInit : Expr OO Γ (.prod BV256 U32))
    (mksInit : Expr OO Γ (.list (.prod BV256 U32)))
    (targetCtr : Expr OO Γ U32) :
    Comp OO I Γ (chainAdvAccT ℓ) :=
  .bind (.ret (.pair (.nat 2000) (.pair targetCtr (.some (.pair ckInit mksInit)))))
    (.iter 25000
      (.snd (.snd .v0))
      (.ret
        (.caseOpt .v0
          .none
          (.ite (e2ePureOp .u32Lt (.pair (.snd (.fst .v0)) (.fst (.snd .v2))))
            (.caseOpt (e2eCryptoOp .chainStep (.fst .v0))
              .none
              (.some
                (.pair (.fst .v0)
                  (.take (.fst .v3)
                    (.cons (.pair (.snd .v0) (.snd (.fst .v1))) (.snd .v1))))))
            (.some .v0)))))

theorem advanceSingleChainC_queries {ι : Type} {T : OracleSpec ι} (I : Iface S T) {Γ}
    (ckInit : Expr OO Γ (.prod BV256 U32))
    (mksInit : Expr OO Γ (.list (.prod BV256 U32)))
    (targetCtr : Expr OO Γ U32)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    (advanceSingleChainC I ckInit mksInit targetCtr).queries w ws = 0 := by
  simp [advanceSingleChainC, Comp.queries]

theorem advanceSingleChainC_cost_le {ι : Type} {T : OracleSpec ι} (I : Iface S T) {Γ}
    (ckInit : Expr OO Γ (.prod BV256 U32))
    (mksInit : Expr OO Γ (.list (.prod BV256 U32)))
    (targetCtr : Expr OO Γ U32) :
    (advanceSingleChainC (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I ckInit mksInit targetCtr).cost ≤
      ckInit.cost + mksInit.cost + targetCtr.cost + 1000025 := by
  simp only [advanceSingleChainC, Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    cost_e2ePureOp, cost_e2eCryptoOp, E2EPureOp.cost, E2ECryptoOp.cost]
  have hb : bits 2000 = 11 := by decide
  rw [hb]
  omega

private theorem iterM_pure {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    (f : α → α) : ∀ (n : ℕ) (a : α), iterM (fun x => (pure (f x) : m α)) n a = pure (f^[n] a)
  | 0, a => rfl
  | n + 1, a => by
    simp [iterM, iterM_pure f n (f a), Function.iterate_succ_apply]

theorem advanceSingleChainC_eval_iterate {ι : Type} {T : OracleSpec ι} (I : Iface S T) {Γ}
    (ckInit : Expr OO Γ (.prod BV256 U32))
    (mksInit : Expr OO Γ (.list (.prod BV256 U32)))
    (targetCtr : Expr OO Γ U32) (ρ : Env Γ) :
    (advanceSingleChainC (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I ckInit mksInit targetCtr).eval ρ =
      pure ((chainAdvStepFn C.F (targetCtr.eval ρ))^[25000]
        (some (ckInit.eval ρ, mksInit.eval ρ))) := by
  simp only [advanceSingleChainC, Comp.eval, Expr.eval, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    Env.get, pure_bind, eval_e2ePureOp, eval_e2eCryptoOp, E2EPureOp.eval]
  rw [← iterM_pure (chainAdvStepFn C.F (targetCtr.eval ρ)) 25000
    (some (ckInit.eval ρ, mksInit.eval ρ))]
  congr 1
  funext a
  congr 1
  rcases a with _ | ⟨⟨ck, idx⟩, mks⟩
  · rfl
  · dsimp only [chainAdvStepFn, E2ECryptoOp.eval]
    simp only [decide_eq_true_eq]
    by_cases hlt : idx < targetCtr.eval ρ
    · simp only [hlt, ↓reduceIte]
      rcases hnext : ChainKey.nextChainKey C.F { key := ck, index := idx } with _ | ckNext <;> rfl
    · simp only [hlt, ↓reduceIte]

end ExprCombinators

/-! ## Equivalence with `RatchetState.advanceChain` -/

private theorem dropLast_eq_take_pred {α : Type} :
    ∀ (l : List α), l.dropLast = l.take (l.length - 1)
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
    simp [List.dropLast, List.take_succ_cons, dropLast_eq_take_pred (b :: rest)]

theorem storeSkipped_trim_eq_take2000 {α : Type} (l : List α) (h : l.length ≤ 2001) :
    (if maxMessageKeys < l.length then l.dropLast else l) = l.take 2000 := by
  have hmax : maxMessageKeys = 2000 := rfl
  rw [hmax]
  by_cases hgt : 2000 < l.length
  · simp only [hgt, ↓reduceIte]
    have hlen : l.length = 2001 := by omega
    rw [dropLast_eq_take_pred, hlen]
  · simp only [hgt, ↓reduceIte]
    exact (List.take_of_length_le (by omega)).symm

private theorem chainAdvStepFn_noop (F : ShaCompress) (targetCtr : BitVec 32)
    (ck : BitVec 256) (idx : BitVec 32) (mks : List (BitVec 256 × BitVec 32))
    (hge : ¬ (idx < targetCtr)) :
    ∀ (n : ℕ), (chainAdvStepFn F targetCtr)^[n] (some ((ck, idx), mks)) =
      some ((ck, idx), mks)
  | 0 => rfl
  | n + 1 => by
    have h1 : chainAdvStepFn F targetCtr (some ((ck, idx), mks)) = some ((ck, idx), mks) := by
      simp [chainAdvStepFn, hge]
    rw [Function.iterate_succ_apply, h1, chainAdvStepFn_noop F targetCtr ck idx mks hge n]

private theorem findIdx?_set_same_key (rcs : List ReceiverChain) (their : PublicKey)
    {i : ℕ} {rc : ReceiverChain} (rc' : ReceiverChain)
    (hfind : rcs.findIdx? (fun c => c.senderRatchetKey == their) = some i)
    (hget : rcs[i]? = some rc)
    (hsrk : rc'.senderRatchetKey = rc.senderRatchetKey) :
    (rcs.set i rc').findIdx? (fun c => c.senderRatchetKey == their) = some i := by
  have hpred : ∀ (x y : ReceiverChain), x.senderRatchetKey = y.senderRatchetKey →
      (x.senderRatchetKey == their) = (y.senderRatchetKey == their) := by
    intro x y hxy; rw [hxy]
  induction rcs generalizing i with
  | nil => simp at hfind
  | cons hd tl ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst hget
      simp only [List.set_cons_zero, List.findIdx?_cons] at hfind ⊢
      rw [hpred rc' hd hsrk]
      cases hhd : hd.senderRatchetKey == their
      · rw [hhd] at hfind
        rcases Option.mem_map.mp hfind with ⟨j, _, hj⟩
        omega
      · rfl
    | succ j =>
      simp only [List.getElem?_cons_succ] at hget
      simp only [List.findIdx?_cons, List.set_cons_succ] at hfind ⊢
      cases hhd : hd.senderRatchetKey == their
      · rw [hhd] at hfind
        rcases Option.mem_map.mp hfind with ⟨k, hk, hk_eq⟩
        have hkj : k = j := by omega
        subst hkj
        rw [ih hk hget]
        simp
      · rw [hhd] at hfind
        cases hfind

private theorem mut_exec_bind_r {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    (m >>= f).exec s =
      match m.exec s with
      | (.error e, s') => (.error e, s')
      | (.ok a, s') => (f a).exec s' := by
  unfold Mut.exec
  rw [ExceptT.run_bind, StateT.run_bind]
  rcases StateT.run (ExceptT.run m) s with ⟨err | val, s'⟩ <;> rfl

/-- Iterating `chainAdvStepFn` at least `(counter - ck.index).toNat` times agrees with `RatchetState.advanceChain`. -/
theorem chainAdvStepFn_iterate_eq_advanceChain (F : ShaCompress) (their : PublicKey)
    (counter : BitVec 32) :
    ∀ (fuel n : ℕ) (ck : ChainKey) (r : RatchetState) (chainIdx : ℕ) (rc : ReceiverChain),
      ck.index ≤ counter →
      counter.toNat - ck.index.toNat = fuel →
      fuel ≤ n →
      r.findReceiverChainIndex their = some chainIdx →
      r.receiverChains[chainIdx]? = some rc →
      rc.messageKeys.length ≤ 2000 →
      (chainAdvStepFn F counter)^[n]
          (some ((ck.key, ck.index), rc.messageKeys.map encodeMsgKey)) =
        match (RatchetState.advanceChain F their counter fuel ck).exec r with
        | (.ok ckOut, rOut) =>
          match rOut.receiverChains[chainIdx]? with
          | some rcOut => some ((ckOut.key, ckOut.index), rcOut.messageKeys.map encodeMsgKey)
          | none => none
        | (.error _, _) => none
  | 0, n, ck, r, chainIdx, rc, hle, hfuel, _, _, hget, _ => by
    have hle_nat : ck.index.toNat ≤ counter.toNat := BitVec.le_def.mp hle
    have heq_nat : ck.index.toNat = counter.toNat := by omega
    have hnot_lt : ¬ (ck.index < counter) := by
      rw [BitVec.lt_def]; omega
    have hexec : (RatchetState.advanceChain F their counter 0 ck).exec r = (.ok ck, r) := rfl
    rw [hexec]
    dsimp only
    rw [hget]
    exact chainAdvStepFn_noop F counter ck.key ck.index (rc.messageKeys.map encodeMsgKey) hnot_lt n
  | fuel + 1, 0, _, _, _, _, _, _, hfn, _, _, _ => by omega
  | fuel + 1, n + 1, ck, r, chainIdx, rc, hle, hfuel, hfn, hfind, hget, hmk_le => by
    have hlt_nat : ck.index.toNat < counter.toNat := by omega
    have hlt : ck.index < counter := BitVec.lt_def.mpr hlt_nat
    have hmax_lt : counter.toNat < 2 ^ 32 := counter.isLt
    have hnot_max : ck.index ≠ BitVec.allOnes 32 := by
      intro hall
      rw [hall, BitVec.toNat_allOnes] at hlt_nat
      omega
    have hnext : ck.nextChainKey F =
        .ok ⟨bytesToKey32 (CryptoGames.Ratchet.chainHmac F ck.key
          CryptoGames.Ratchet.chainKeySeed), ck.index + 1⟩ := by
      unfold ChainKey.nextChainKey
      simp only [hnot_max, ↓reduceIte]
    let ck' : ChainKey :=
      ⟨bytesToKey32 (CryptoGames.Ratchet.chainHmac F ck.key CryptoGames.Ratchet.chainKeySeed),
       ck.index + 1⟩
    let keys1 : List MessageKeyGenerator := (ck.messageKeys F :: rc.messageKeys).take 2000
    let rc1 : ReceiverChain := { rc with messageKeys := keys1 }
    let r1 : RatchetState := { r with receiverChains := r.receiverChains.set chainIdx rc1 }
    have hstore : (RatchetState.storeSkippedKey their (ck.messageKeys F)).exec r = (.ok (), r1) := by
      unfold RatchetState.storeSkippedKey
      rw [mut_exec_bind_r]
      have hgetS : (get : Mut RatchetState RatchetState).exec r = (.ok r, r) := rfl
      rw [hgetS]
      dsimp only
      rw [hfind]
      dsimp only
      rw [hget]
      dsimp only
      have htrim : (if maxMessageKeys < (ck.messageKeys F :: rc.messageKeys).length then
            (ck.messageKeys F :: rc.messageKeys).dropLast
          else ck.messageKeys F :: rc.messageKeys) = keys1 :=
        storeSkipped_trim_eq_take2000 _ (by simp; omega)
      rw [htrim]
      rfl
    have hadv_step : (RatchetState.advanceChain F their counter (fuel + 1) ck).exec r =
        (RatchetState.advanceChain F their counter fuel ck').exec r1 := by
      conv_lhs => unfold RatchetState.advanceChain
      simp only [hlt, ↓reduceIte]
      rw [mut_exec_bind_r, hstore]
      dsimp only
      rw [mut_exec_bind_r]
      have hlift : (liftE (σ := RatchetState) (ck.nextChainKey F)).exec r1 = (.ok ck', r1) := by
        rw [hnext]; rfl
      rw [hlift]
    have hstep1 : chainAdvStepFn F counter
        (some ((ck.key, ck.index), rc.messageKeys.map encodeMsgKey)) =
        some ((ck'.key, ck'.index), rc1.messageKeys.map encodeMsgKey) := by
      dsimp only [chainAdvStepFn]
      simp only [hlt, ↓reduceIte]
      have hck_eq : ({ key := ck.key, index := ck.index } : ChainKey) = ck := by
        cases ck; rfl
      rw [hck_eq, hnext]
      dsimp only [rc1, keys1]
      rw [List.map_take, List.map_cons]
      rfl
    have hidx1_nat : ck'.index.toNat = ck.index.toNat + 1 := by
      dsimp only [ck']
      rw [BitVec.toNat_add]
      change (ck.index.toNat + 1) % 4294967296 = ck.index.toNat + 1
      omega
    have hle1 : ck'.index ≤ counter := BitVec.le_def.mpr (by omega)
    have hfuel1 : counter.toNat - ck'.index.toNat = fuel := by omega
    have hlt_len : chainIdx < r.receiverChains.length :=
      (List.getElem?_eq_some_iff.mp hget).1
    have hget1 : r1.receiverChains[chainIdx]? = some rc1 := by
      dsimp only [r1]
      exact List.getElem?_set_self hlt_len
    have hfind1 : r1.findReceiverChainIndex their = some chainIdx := by
      dsimp only [RatchetState.findReceiverChainIndex, r1] at hfind ⊢
      exact findIdx?_set_same_key r.receiverChains their rc1 hfind hget rfl
    have hmk1_le : rc1.messageKeys.length ≤ 2000 :=
      List.length_take_le 2000 _
    rw [Function.iterate_succ_apply, hstep1, hadv_step]
    exact chainAdvStepFn_iterate_eq_advanceChain F their counter fuel n ck' r1 chainIdx rc1
      hle1 hfuel1 (by omega) hfind1 hget1 hmk1_le

end Computational.Proofs.E2E.Dsl.DrSessionSimHooks

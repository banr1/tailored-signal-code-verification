/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.SmReachInv
public import Computational.Proofs.E2E.Dsl.TablesHonest
public import Computational.Proofs.E2E.Dsl.ClampsLossless

/-!
# Wire Wrappers, Response Codecs, and Linear-Size SM Bookkeeping

Defines `ReductionDsl.Expr` building blocks over `e2eSig ℓ` for wire framing, curve canonicality
checks, and `SM.spec` response codecs. Introduces a deduplicated, compromise-cached encoding
`e2eGsEnc` of `SM.GameState` into `e2eGsTy ℓ` under which every pure SM bookkeeping operation runs
in `O(q)` static cost under `SmListBounded q s`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping

open List Option Bool Prod Sum
open ReductionDsl (Sig Ty Var Env Ops Iface Expr bits)
open CryptoGames (Party SMScheme)
open CryptoGames.CBC (Plain)
open CryptoGames.SM (Pos Record RecvResult GameState healedBy maxOpt inWindow noBobSendInEpoch0
  noAliceCorrWhileAliceBelowEpoch10 partyEnc partyDec posTy posEnc posDec posSender posEpoch posIdx
  posEq orE boolEq leN maxN minN isSomeE otherE sendsInE pGet pSet maxAccGet maxAccSet healedByE
  maxOptE letE_eval ite_eval pair_eval some_eval orE_eval boolEq_eval leN_eval maxN_eval minN_eval
  isSomeE_eval otherE_eval sendsInE_eval pGet_eval pSet_eval posEq_eval healedByE_eval maxOptE_eval
  find?_map_eq any_map_eq foldr_filter_map any_beq_eq_contains)
open CryptoGames.Ratchet.LibsignalInst (ratchetKeyAdmissible configR1OnCurve)
open CryptoGames.LibsignalSession (Crypto PublicKey GhostState)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (Bytes wirePrekey wireWhisper noBobCorrInEpoch0
  noBobCorrWhileAliceBelowEpoch10 configRefuseEarlyBobCorr BHE2ESmResp bhPackSmResp)
open CryptoVerification.E2E.Costed (e2eSig B U32 PK PlainT GhostStT hdrT hdrV hdrOfV
  recvResultT recvResultEnc recvResultDec partyToBool boolToParty smRT smRdec
  E2EPureOp E2ECurveCheckOp e2ePureOps e2eCurveCheckOps e2eAdapterOps e2eOps
  e2eDecodePreKeyMsg e2eHdrOfPreKeyMsg e2eExpectedPreKeyMsg e2ePartneredInnerBytes
  e2eWireInnerBytes)
open Computational.Proofs.E2E.Dsl.TablesHonest (e2ePureOp e2eCurveOp eval_e2ePureOp cost_e2ePureOp
  eval_e2eCurveOp cost_e2eCurveOp adapterPureOp adapterCurveOp eval_adapterPureOp
  cost_adapterPureOp eval_adapterCurveOp cost_adapterCurveOp recvResultDec_recvResultEnc)
open Computational.Proofs.E2E.Dsl.ClampsLossless (e2ePureOps_eval_wrapWhisperWire_lossless
  e2ePureOps_eval_wrapPreKeyWire_lossless e2ePureOps_eval_parsePreKeyWire_lossless
  e2ePartneredInnerBytes_lossless e2eWireInnerBytes_lossless)
open Computational.Proofs.E2E.Dsl.SmReachInv (dedupComp mem_dedupComp dedupComp_contains
  dedupComp_filter dedupComp_afterCorr_eq SmListBounded)

/-! ## Wire and curve-check `Expr` wrappers -/

section WireAndCurveOps

variable {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

local notation "S" => e2eSig ℓ
local notation "OO" => e2eOps ℓ P C K decT encT
local notation "AO" => e2eAdapterOps ℓ decT encT

def bytesEqE {Γ : List (Ty S)} (a b : Expr OO Γ (B 32)) : Expr OO Γ .bool :=
  e2ePureOp (.bytesEq 32 32) (.pair a b)

@[simp] theorem eval_bytesEqE {Γ : List (Ty S)} (a b : Expr OO Γ (B 32)) (ρ : Env Γ) :
    (bytesEqE a b).eval ρ = (a.eval ρ == b.eval ρ) := rfl

@[simp] theorem cost_bytesEqE {Γ : List (Ty S)} (a b : Expr OO Γ (B 32)) :
    (bytesEqE a b).cost = a.cost + b.cost + 65 := by
  have h32 : ((32 : ℕ+) : ℕ) = 32 := rfl
  simp only [bytesEqE, cost_e2ePureOp, E2EPureOp.cost, Expr.cost, h32]

def wrapWhisperWireE {Γ : List (Ty S)} (ct : Expr OO Γ (B 32)) : Expr OO Γ (B 32) :=
  e2ePureOp .wrapWhisperWire ct

@[simp] theorem eval_wrapWhisperWireE {Γ : List (Ty S)} (ct : Expr OO Γ (B 32)) (ρ : Env Γ) :
    (wrapWhisperWireE ct).eval ρ = (e2ePureOps ℓ).eval .wrapWhisperWire (ct.eval ρ) := rfl

theorem eval_wrapWhisperWireE_lossless {Γ : List (Ty S)} (ct : Expr OO Γ (B 32)) (ρ : Env Γ)
    (hct : (ct.eval ρ).length < 32 * (2 * (ℓ / 32) + 26)) :
    (wrapWhisperWireE ct).eval ρ =
      if (ct.eval ρ).isEmpty then [] else wireWhisper :: ct.eval ρ :=
  e2ePureOps_eval_wrapWhisperWire_lossless ℓ (ct.eval ρ) hct

@[simp] theorem cost_wrapWhisperWireE {Γ : List (Ty S)} (ct : Expr OO Γ (B 32)) :
    (wrapWhisperWireE ct).cost = ct.cost + (2 * (ℓ / 32) + 28) := rfl

def wrapPreKeyWireE {Γ : List (Ty S)} (regIdA : Expr OO Γ U32) (hdr : Expr OO Γ hdrT)
    (inner : Expr OO Γ (B 32)) : Expr OO Γ (B 32) :=
  e2ePureOp .wrapPreKeyWire (.pair regIdA (.pair hdr inner))

@[simp] theorem eval_wrapPreKeyWireE {Γ : List (Ty S)} (regIdA : Expr OO Γ U32)
    (hdr : Expr OO Γ hdrT) (inner : Expr OO Γ (B 32)) (ρ : Env Γ) :
    (wrapPreKeyWireE regIdA hdr inner).eval ρ =
      (e2ePureOps ℓ).eval .wrapPreKeyWire (regIdA.eval ρ, (hdr.eval ρ, inner.eval ρ)) := rfl

theorem eval_wrapPreKeyWireE_lossless {Γ : List (Ty S)} (regIdA : Expr OO Γ U32)
    (hdr : Expr OO Γ hdrT) (inner : Expr OO Γ (B 32)) (ρ : Env Γ)
    (hinner : (inner.eval ρ).length ≤ 32 * (ℓ / 32) + 512) :
    (wrapPreKeyWireE regIdA hdr inner).eval ρ =
      if (inner.eval ρ).isEmpty then []
      else wirePrekey ::
        (e2eExpectedPreKeyMsg (regIdA.eval ρ) (hdrOfV (hdr.eval ρ)) (inner.eval ρ)).bytes :=
  e2ePureOps_eval_wrapPreKeyWire_lossless ℓ (regIdA.eval ρ) (hdr.eval ρ) (inner.eval ρ) hinner

@[simp] theorem cost_wrapPreKeyWireE {Γ : List (Ty S)} (regIdA : Expr OO Γ U32)
    (hdr : Expr OO Γ hdrT) (inner : Expr OO Γ (B 32)) :
    (wrapPreKeyWireE regIdA hdr inner).cost =
      regIdA.cost + hdr.cost + inner.cost + (2 * (ℓ / 32) + 90) := by
  simp only [wrapPreKeyWireE, cost_e2ePureOp, E2EPureOp.cost, Expr.cost]
  omega

def parsePreKeyWireE {Γ : List (Ty S)} (c : Expr OO Γ (B 32)) :
    Expr OO Γ (.opt (.prod U32 (.prod hdrT (B 32)))) :=
  e2ePureOp .parsePreKeyWire c

@[simp] theorem eval_parsePreKeyWireE {Γ : List (Ty S)} (c : Expr OO Γ (B 32)) (ρ : Env Γ) :
    (parsePreKeyWireE c).eval ρ =
      (e2eDecodePreKeyMsg (c.eval ρ)).map
        fun m => (m.regId, (hdrV (e2eHdrOfPreKeyMsg m), m.inner)) :=
  e2ePureOps_eval_parsePreKeyWire_lossless ℓ (c.eval ρ)

@[simp] theorem cost_parsePreKeyWireE {Γ : List (Ty S)} (c : Expr OO Γ (B 32)) :
    (parsePreKeyWireE c).cost = c.cost + 96 := rfl

def partneredInnerBytesE {Γ : List (Ty S)} (bobAcc : Expr OO Γ .bool) (regIdA : Expr OO Γ U32)
    (hdr : Expr OO Γ hdrT) (c : Expr OO Γ (B 32)) : Expr OO Γ (.opt (B 32)) :=
  e2ePureOp .partneredInnerBytes (.pair bobAcc (.pair regIdA (.pair hdr c)))

@[simp] theorem eval_partneredInnerBytesE {Γ : List (Ty S)} (bobAcc : Expr OO Γ .bool)
    (regIdA : Expr OO Γ U32) (hdr : Expr OO Γ hdrT) (c : Expr OO Γ (B 32)) (ρ : Env Γ) :
    (partneredInnerBytesE bobAcc regIdA hdr c).eval ρ =
      e2ePartneredInnerBytes (bobAcc.eval ρ) (regIdA.eval ρ) (hdrOfV (hdr.eval ρ)) (c.eval ρ) :=
  rfl

theorem eval_partneredInnerBytesE_lossless {Γ : List (Ty S)} (bobAcc : Expr OO Γ .bool)
    (regIdA : Expr OO Γ U32) (hdr : Expr OO Γ hdrT) (c : Expr OO Γ (B 32)) (ρ : Env Γ) :
    (partneredInnerBytesE bobAcc regIdA hdr c).eval ρ =
      let cb : Bytes := c.eval ρ
      if !(bobAcc.eval ρ) then
        match e2eDecodePreKeyMsg cb with
        | some m =>
          if cb ==
              wirePrekey :: (e2eExpectedPreKeyMsg (regIdA.eval ρ) (hdrOfV (hdr.eval ρ)) m.inner).bytes
          then some m.inner
          else none
        | none => none
      else
        match e2eDecodePreKeyMsg cb with
        | some m =>
          if e2eHdrOfPreKeyMsg m == hdrOfV (hdr.eval ρ) then some m.inner else none
        | none =>
          match cb with
          | t :: body => if t == wireWhisper then some body else none
          | [] => none := by
  rw [eval_partneredInnerBytesE]
  exact e2ePartneredInnerBytes_lossless (bobAcc.eval ρ) (regIdA.eval ρ) (hdrOfV (hdr.eval ρ)) (c.eval ρ)

@[simp] theorem cost_partneredInnerBytesE {Γ : List (Ty S)} (bobAcc : Expr OO Γ .bool)
    (regIdA : Expr OO Γ U32) (hdr : Expr OO Γ hdrT) (c : Expr OO Γ (B 32)) :
    (partneredInnerBytesE bobAcc regIdA hdr c).cost =
      bobAcc.cost + regIdA.cost + hdr.cost + c.cost + 131 := by
  simp only [partneredInnerBytesE, cost_e2ePureOp, E2EPureOp.cost, Expr.cost]
  omega

def wireInnerBytesE {Γ : List (Ty S)} (c : Expr OO Γ (B 32)) : Expr OO Γ (.opt (B 32)) :=
  e2ePureOp .wireInnerBytes c

@[simp] theorem eval_wireInnerBytesE {Γ : List (Ty S)} (c : Expr OO Γ (B 32)) (ρ : Env Γ) :
    (wireInnerBytesE c).eval ρ = e2eWireInnerBytes (c.eval ρ) := rfl

theorem eval_wireInnerBytesE_lossless {Γ : List (Ty S)} (c : Expr OO Γ (B 32)) (ρ : Env Γ) :
    (wireInnerBytesE c).eval ρ =
      let cb : Bytes := c.eval ρ
      match e2eDecodePreKeyMsg cb with
      | some m => some m.inner
      | none =>
        match cb with
        | t :: body => if t == wireWhisper then some body else none
        | [] => none := by
  rw [eval_wireInnerBytesE]
  exact e2eWireInnerBytes_lossless (c.eval ρ)

@[simp] theorem cost_wireInnerBytesE {Γ : List (Ty S)} (c : Expr OO Γ (B 32)) :
    (wireInnerBytesE c).cost = c.cost + 96 := rfl

def decEncCheckE {Γ : List (Ty S)} (pk : Expr OO Γ PK) : Expr OO Γ .bool :=
  e2eCurveOp .decEncCheck pk

@[simp] theorem eval_decEncCheckE {Γ : List (Ty S)} (pk : Expr OO Γ PK) (ρ : Env Γ) :
    (decEncCheckE (P := P) (C := C) (K := K) (decT := decT) (encT := encT) pk).eval ρ =
      match decT (pk.eval ρ) with
      | some T => decide (encT T = pk.eval ρ)
      | none => false := rfl

@[simp] theorem cost_decEncCheckE {Γ : List (Ty S)} (pk : Expr OO Γ PK) :
    (decEncCheckE (P := P) (C := C) (K := K) (decT := decT) (encT := encT) pk).cost =
      pk.cost + 8 := rfl

def ratchetKeyAdmissibleE {Γ : List (Ty S)} (c : Expr OO Γ (B 32)) : Expr OO Γ .bool :=
  e2eCurveOp .checkRatchetKeyOnCurve c

@[simp] theorem eval_ratchetKeyAdmissibleE {Γ : List (Ty S)} (c : Expr OO Γ (B 32)) (ρ : Env Γ) :
    (ratchetKeyAdmissibleE (P := P) (C := C) (K := K) (decT := decT) (encT := encT) c).eval ρ =
      ratchetKeyAdmissible protoSignalCodec decT encT (c.eval ρ) := rfl

@[simp] theorem cost_ratchetKeyAdmissibleE {Γ : List (Ty S)} (c : Expr OO Γ (B 32)) :
    (ratchetKeyAdmissibleE (P := P) (C := C) (K := K) (decT := decT) (encT := encT) c).cost =
      c.cost + (ℓ / 32 + 24) := rfl

def adapterWrapWhisperWireE {Γ : List (Ty S)} (ct : Expr AO Γ (B 32)) : Expr AO Γ (B 32) :=
  adapterPureOp .wrapWhisperWire ct

@[simp] theorem eval_adapterWrapWhisperWireE {Γ : List (Ty S)} (ct : Expr AO Γ (B 32)) (ρ : Env Γ) :
    (adapterWrapWhisperWireE ct).eval ρ = (e2ePureOps ℓ).eval .wrapWhisperWire (ct.eval ρ) := rfl

@[simp] theorem cost_adapterWrapWhisperWireE {Γ : List (Ty S)} (ct : Expr AO Γ (B 32)) :
    (adapterWrapWhisperWireE ct).cost = ct.cost + (2 * (ℓ / 32) + 28) := rfl

def adapterWrapPreKeyWireE {Γ : List (Ty S)} (regIdA : Expr AO Γ U32) (hdr : Expr AO Γ hdrT)
    (inner : Expr AO Γ (B 32)) : Expr AO Γ (B 32) :=
  adapterPureOp .wrapPreKeyWire (.pair regIdA (.pair hdr inner))

@[simp] theorem eval_adapterWrapPreKeyWireE {Γ : List (Ty S)} (regIdA : Expr AO Γ U32)
    (hdr : Expr AO Γ hdrT) (inner : Expr AO Γ (B 32)) (ρ : Env Γ) :
    (adapterWrapPreKeyWireE regIdA hdr inner).eval ρ =
      (e2ePureOps ℓ).eval .wrapPreKeyWire (regIdA.eval ρ, (hdr.eval ρ, inner.eval ρ)) := rfl

@[simp] theorem cost_adapterWrapPreKeyWireE {Γ : List (Ty S)} (regIdA : Expr AO Γ U32)
    (hdr : Expr AO Γ hdrT) (inner : Expr AO Γ (B 32)) :
    (adapterWrapPreKeyWireE regIdA hdr inner).cost =
      regIdA.cost + hdr.cost + inner.cost + (2 * (ℓ / 32) + 90) := by
  simp only [adapterWrapPreKeyWireE, cost_adapterPureOp, E2EPureOp.cost, Expr.cost]
  omega

def adapterParsePreKeyWireE {Γ : List (Ty S)} (c : Expr AO Γ (B 32)) :
    Expr AO Γ (.opt (.prod U32 (.prod hdrT (B 32)))) :=
  adapterPureOp .parsePreKeyWire c

@[simp] theorem eval_adapterParsePreKeyWireE {Γ : List (Ty S)} (c : Expr AO Γ (B 32)) (ρ : Env Γ) :
    (adapterParsePreKeyWireE c).eval ρ =
      (e2eDecodePreKeyMsg (c.eval ρ)).map
        fun m => (m.regId, (hdrV (e2eHdrOfPreKeyMsg m), m.inner)) :=
  e2ePureOps_eval_parsePreKeyWire_lossless ℓ (c.eval ρ)

@[simp] theorem cost_adapterParsePreKeyWireE {Γ : List (Ty S)} (c : Expr AO Γ (B 32)) :
    (adapterParsePreKeyWireE c).cost = c.cost + 96 := rfl

def adapterPartneredInnerBytesE {Γ : List (Ty S)} (bobAcc : Expr AO Γ .bool)
    (regIdA : Expr AO Γ U32) (hdr : Expr AO Γ hdrT) (c : Expr AO Γ (B 32)) :
    Expr AO Γ (.opt (B 32)) :=
  adapterPureOp .partneredInnerBytes (.pair bobAcc (.pair regIdA (.pair hdr c)))

@[simp] theorem eval_adapterPartneredInnerBytesE {Γ : List (Ty S)} (bobAcc : Expr AO Γ .bool)
    (regIdA : Expr AO Γ U32) (hdr : Expr AO Γ hdrT) (c : Expr AO Γ (B 32)) (ρ : Env Γ) :
    (adapterPartneredInnerBytesE bobAcc regIdA hdr c).eval ρ =
      e2ePartneredInnerBytes (bobAcc.eval ρ) (regIdA.eval ρ) (hdrOfV (hdr.eval ρ)) (c.eval ρ) :=
  rfl

@[simp] theorem cost_adapterPartneredInnerBytesE {Γ : List (Ty S)} (bobAcc : Expr AO Γ .bool)
    (regIdA : Expr AO Γ U32) (hdr : Expr AO Γ hdrT) (c : Expr AO Γ (B 32)) :
    (adapterPartneredInnerBytesE bobAcc regIdA hdr c).cost =
      bobAcc.cost + regIdA.cost + hdr.cost + c.cost + 131 := by
  simp only [adapterPartneredInnerBytesE, cost_adapterPureOp, E2EPureOp.cost, Expr.cost]
  omega

def adapterWireInnerBytesE {Γ : List (Ty S)} (c : Expr AO Γ (B 32)) : Expr AO Γ (.opt (B 32)) :=
  adapterPureOp .wireInnerBytes c

@[simp] theorem eval_adapterWireInnerBytesE {Γ : List (Ty S)} (c : Expr AO Γ (B 32)) (ρ : Env Γ) :
    (adapterWireInnerBytesE c).eval ρ = e2eWireInnerBytes (c.eval ρ) := rfl

@[simp] theorem cost_adapterWireInnerBytesE {Γ : List (Ty S)} (c : Expr AO Γ (B 32)) :
    (adapterWireInnerBytesE c).cost = c.cost + 96 := rfl

def adapterRatchetKeyAdmissibleE {Γ : List (Ty S)} (c : Expr AO Γ (B 32)) : Expr AO Γ .bool :=
  adapterCurveOp .checkRatchetKeyOnCurve c

@[simp] theorem eval_adapterRatchetKeyAdmissibleE {Γ : List (Ty S)} (c : Expr AO Γ (B 32))
    (ρ : Env Γ) :
    (adapterRatchetKeyAdmissibleE (decT := decT) (encT := encT) c).eval ρ =
      ratchetKeyAdmissible protoSignalCodec decT encT (c.eval ρ) := rfl

@[simp] theorem cost_adapterRatchetKeyAdmissibleE {Γ : List (Ty S)} (c : Expr AO Γ (B 32)) :
    (adapterRatchetKeyAdmissibleE (decT := decT) (encT := encT) c).cost =
      c.cost + (ℓ / 32 + 24) := rfl

end WireAndCurveOps

/-! ## Response codecs and `Expr` builders -/

@[simp] theorem partyToBool_eq_partyEnc (p : Party) : partyToBool p = partyEnc p := by
  cases p <;> rfl

@[simp] theorem boolToParty_eq_partyDec (b : Bool) : boolToParty b = partyDec b := by
  cases b <;> rfl

/-- Encode an `SM.spec` response into `smRT stT`. -/
def smRenc {ℓ : ℕ} {St : Type} {stT : Ty (e2eSig ℓ)} (toSt : St → stT.denote) :
    (sq : (CryptoGames.SM.spec St (Plain ℓ) (BitVec 512) Bytes).Domain) →
    (CryptoGames.SM.spec St (Plain ℓ) (BitVec 512) Bytes).Range sq →
    (smRT (ℓ := ℓ) stT).denote
  | .inl (.inl (.inl (.inl _))), w => (w, (none, none))
  | .inl (.inl (.inl (.inr _))), w => (w, (none, none))
  | .inl (.inl (.inr _)), rr => (none, (rr.map recvResultEnc, none))
  | .inl (.inr _), rr => (none, (rr.map recvResultEnc, none))
  | .inr _, st? => (none, (none, st?.map toSt))

theorem smRdec_smRenc {ℓ : ℕ} {St : Type} {stT : Ty (e2eSig ℓ)}
    (ofSt : stT.denote → St) (toSt : St → stT.denote)
    (hrt : ∀ x, ofSt (toSt x) = x)
    (sq : (CryptoGames.SM.spec St (Plain ℓ) (BitVec 512) Bytes).Domain)
    (r : (CryptoGames.SM.spec St (Plain ℓ) (BitVec 512) Bytes).Range sq) :
    smRdec (stT := stT) ofSt sq (smRenc (stT := stT) toSt sq r) = r := by
  rcases sq with (((_ | _) | _) | _) | _
  · rfl
  · rfl
  · cases r <;> simp [smRenc, smRdec]
  · cases r <;> simp [smRenc, smRdec]
  · cases r with
    | none => rfl
    | some x => simp [smRenc, smRdec, hrt x]

@[simp] theorem smRdec_smRenc_id {ℓ : ℕ}
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (r : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range sq) :
    smRdec (stT := GhostStT) id sq (smRenc (stT := GhostStT) id sq r) = r :=
  smRdec_smRenc (stT := GhostStT) id id (fun _ => rfl) sq r

theorem smRenc_id_eq_bhPackSmResp {ℓ : ℕ}
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (r : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range sq) :
    let packed := bhPackSmResp sq r
    smRenc (stT := GhostStT) id sq r =
      (packed.1, (packed.2.1.map recvResultEnc, packed.2.2)) := by
  rcases sq with (((_ | _) | _) | _) | _ <;> simp [smRenc, bhPackSmResp]

section RespExprs

variable {ℓ : ℕ} {O' : Ops (e2eSig ℓ)}

def recvResultRejE {Γ : List (Ty (e2eSig ℓ))} : Expr O' Γ recvResultT :=
  .inl .unit

def recvResultAccE {Γ : List (Ty (e2eSig ℓ))}
    (t i : Expr O' Γ .nat) (m? : Expr O' Γ (.opt PlainT)) : Expr O' Γ recvResultT :=
  .inr (.pair t (.pair i m?))

def smRWireE {stT : Ty (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    (w? : Expr O' Γ (.opt (B 32))) : Expr O' Γ (smRT stT) :=
  .pair w? (.pair .none .none)

def smRRecvE {stT : Ty (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    (rr? : Expr O' Γ (.opt recvResultT)) : Expr O' Γ (smRT stT) :=
  .pair .none (.pair rr? .none)

def smRCorrE {stT : Ty (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    (st? : Expr O' Γ (.opt stT)) : Expr O' Γ (smRT stT) :=
  .pair .none (.pair .none st?)

@[simp] theorem eval_recvResultRejE {Γ : List (Ty (e2eSig ℓ))} (ρ : Env Γ) :
    (recvResultRejE (O' := O')).eval ρ = recvResultEnc (ℓ := ℓ) .rejected := rfl

@[simp] theorem cost_recvResultRejE {Γ : List (Ty (e2eSig ℓ))} :
    (recvResultRejE (ℓ := ℓ) (O' := O') (Γ := Γ)).cost = 2 := rfl

@[simp] theorem eval_recvResultAccE {Γ : List (Ty (e2eSig ℓ))}
    (t i : Expr O' Γ .nat) (m? : Expr O' Γ (.opt PlainT)) (ρ : Env Γ) :
    (recvResultAccE t i m?).eval ρ =
      recvResultEnc (.accepted (t.eval ρ) (i.eval ρ) (m?.eval ρ)) := rfl

@[simp] theorem cost_recvResultAccE {Γ : List (Ty (e2eSig ℓ))}
    (t i : Expr O' Γ .nat) (m? : Expr O' Γ (.opt PlainT)) :
    (recvResultAccE t i m?).cost = t.cost + i.cost + m?.cost + 3 := by
  simp only [recvResultAccE, Expr.cost]
  omega

@[simp] theorem eval_smRWireE {stT : Ty (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    (w? : Expr O' Γ (.opt (B 32))) (ρ : Env Γ) :
    (smRWireE (stT := stT) w?).eval ρ = (w?.eval ρ, (none, none)) := rfl

@[simp] theorem cost_smRWireE {stT : Ty (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    (w? : Expr O' Γ (.opt (B 32))) :
    (smRWireE (stT := stT) w?).cost = w?.cost + 4 := by
  simp only [smRWireE, Expr.cost]

@[simp] theorem eval_smRRecvE {stT : Ty (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    (rr? : Expr O' Γ (.opt recvResultT)) (ρ : Env Γ) :
    (smRRecvE (stT := stT) rr?).eval ρ = (none, (rr?.eval ρ, none)) := rfl

@[simp] theorem cost_smRRecvE {stT : Ty (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    (rr? : Expr O' Γ (.opt recvResultT)) :
    (smRRecvE (stT := stT) rr?).cost = rr?.cost + 4 := by
  simp only [smRRecvE, Expr.cost]
  omega

@[simp] theorem eval_smRCorrE {stT : Ty (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    (st? : Expr O' Γ (.opt stT)) (ρ : Env Γ) :
    (smRCorrE st?).eval ρ = (none, (none, st?.eval ρ)) := rfl

@[simp] theorem cost_smRCorrE {stT : Ty (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    (st? : Expr O' Γ (.opt stT)) :
    (smRCorrE st?).cost = st?.cost + 4 := by
  simp only [smRCorrE, Expr.cost]
  omega

end RespExprs

/-! ## Linear-size `SM.GameState` bookkeeping -/

/-- `SM.Record (Plain ℓ) Bytes` paired with its cached `comp.contains pos` flag:
`(pos, (msg, (ct, isComp)))`. -/
@[reducible] def e2eRecTy (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod posTy (.prod PlainT (.prod (B 32) .bool))

def e2eRecEncWith {ℓ : ℕ} (comp : List Pos) (r : Record (Plain ℓ) Bytes) :
    (e2eRecTy ℓ).denote :=
  (posEnc r.pos, (r.msg, (r.ct, comp.contains r.pos)))

def e2eRecDec {ℓ : ℕ} (v : (e2eRecTy ℓ).denote) : Record (Plain ℓ) Bytes :=
  ⟨posDec v.1, v.2.1, v.2.2.1⟩

@[simp] theorem e2eRecDec_e2eRecEncWith {ℓ : ℕ} (comp : List Pos) (r : Record (Plain ℓ) Bytes) :
    e2eRecDec (e2eRecEncWith comp r) = r := by
  cases r; simp [e2eRecEncWith, e2eRecDec]

/-- `SM.GameState (GhostState Bytes) (Plain ℓ) Bytes` represented in `e2eSig ℓ` with deduplicated
`comp` (`dedupComp s.comp`) and per-record cached compromise flags. -/
@[reducible] def e2eGsTy (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod (.prod GhostStT GhostStT)
    (.prod .bool
      (.prod .bool
        (.prod (.prod .nat .nat)
          (.prod (.prod .nat .nat)
            (.prod (.opt .nat)
              (.prod (.list (e2eRecTy ℓ))
                (.prod (.list posTy)
                  (.prod (.list posTy)
                    (.prod (.prod (.tbl .nat) (.tbl .nat))
                      (.prod (.list .nat)
                        (.list (.prod .bool .nat))))))))))))

def e2eGsEnc {ℓ : ℕ} (s : GameState (GhostState Bytes) (Plain ℓ) Bytes) :
    (e2eGsTy ℓ).denote :=
  ((s.st .A, s.st .B),
   (s.b,
    (s.win,
     ((s.epoch .A, s.epoch .B),
      ((s.idx .A, s.idx .B),
       (s.tL,
        (s.trans.map (e2eRecEncWith s.comp),
         (s.chall.map posEnc,
          ((dedupComp s.comp).map posEnc,
           ((s.maxAcc .A, s.maxAcc .B),
            (s.leaks,
             s.corrs.map (fun pe => (partyEnc pe.1, pe.2)))))))))))))

def e2eGsDec {ℓ : ℕ} (v : (e2eGsTy ℓ).denote) :
    GameState (GhostState Bytes) (Plain ℓ) Bytes :=
  let (stAB, (b, (win, (epAB, (idxAB, (tL, (trs, (chall, (comp, (maAB, (leaks, corrs))))))))))) := v
  { st := fun | .A => stAB.1 | .B => stAB.2
    epoch := fun | .A => epAB.1 | .B => epAB.2
    idx := fun | .A => idxAB.1 | .B => idxAB.2
    tL := tL
    trans := trs.map e2eRecDec
    chall := chall.map posDec
    comp := comp.map posDec
    maxAcc := fun | .A => maAB.1 | .B => maAB.2
    b := b
    win := win
    leaks := leaks
    corrs := corrs.map (fun pe => (partyDec pe.1, pe.2)) }

section GsBookkeeping

variable {ℓ : ℕ} {O' : Ops (e2eSig ℓ)}

local notation "S" => e2eSig ℓ

def e2eRecPos {Γ : List (Ty S)} (r : Expr O' Γ (e2eRecTy ℓ)) : Expr O' Γ posTy :=
  .fst r

def e2eRecMsg {Γ : List (Ty S)} (r : Expr O' Γ (e2eRecTy ℓ)) : Expr O' Γ PlainT :=
  .fst (.snd r)

def e2eRecCt {Γ : List (Ty S)} (r : Expr O' Γ (e2eRecTy ℓ)) : Expr O' Γ (B 32) :=
  .fst (.snd (.snd r))

def e2eRecComp {Γ : List (Ty S)} (r : Expr O' Γ (e2eRecTy ℓ)) : Expr O' Γ .bool :=
  .snd (.snd (.snd r))

def e2eRecMk {Γ : List (Ty S)} (pos : Expr O' Γ posTy) (msg : Expr O' Γ PlainT)
    (ct : Expr O' Γ (B 32)) (isComp : Expr O' Γ .bool) : Expr O' Γ (e2eRecTy ℓ) :=
  .pair pos (.pair msg (.pair ct isComp))

def e2eGsSt {Γ : List (Ty S)} (s : Expr O' Γ (e2eGsTy ℓ)) :
    Expr O' Γ (.prod GhostStT GhostStT) := .fst s

def e2eGsB {Γ : List (Ty S)} (s : Expr O' Γ (e2eGsTy ℓ)) : Expr O' Γ .bool :=
  .fst (.snd s)

def e2eGsWin {Γ : List (Ty S)} (s : Expr O' Γ (e2eGsTy ℓ)) : Expr O' Γ .bool :=
  .fst (.snd (.snd s))

def e2eGsEpoch {Γ : List (Ty S)} (s : Expr O' Γ (e2eGsTy ℓ)) : Expr O' Γ (.prod .nat .nat) :=
  .fst (.snd (.snd (.snd s)))

def e2eGsIdx {Γ : List (Ty S)} (s : Expr O' Γ (e2eGsTy ℓ)) : Expr O' Γ (.prod .nat .nat) :=
  .fst (.snd (.snd (.snd (.snd s))))

def e2eGsTL {Γ : List (Ty S)} (s : Expr O' Γ (e2eGsTy ℓ)) : Expr O' Γ (.opt .nat) :=
  .fst (.snd (.snd (.snd (.snd (.snd s)))))

def e2eGsTrans {Γ : List (Ty S)} (s : Expr O' Γ (e2eGsTy ℓ)) :
    Expr O' Γ (.list (e2eRecTy ℓ)) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd s))))))

def e2eGsChall {Γ : List (Ty S)} (s : Expr O' Γ (e2eGsTy ℓ)) : Expr O' Γ (.list posTy) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd s)))))))

def e2eGsComp {Γ : List (Ty S)} (s : Expr O' Γ (e2eGsTy ℓ)) : Expr O' Γ (.list posTy) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd s))))))))

def e2eGsMaxAcc {Γ : List (Ty S)} (s : Expr O' Γ (e2eGsTy ℓ)) :
    Expr O' Γ (.prod (.tbl .nat) (.tbl .nat)) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd s)))))))))

def e2eGsLeaks {Γ : List (Ty S)} (s : Expr O' Γ (e2eGsTy ℓ)) : Expr O' Γ (.list .nat) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd s))))))))))

def e2eGsCorrs {Γ : List (Ty S)} (s : Expr O' Γ (e2eGsTy ℓ)) :
    Expr O' Γ (.list (.prod .bool .nat)) :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd s))))))))))

def e2eGsMk {Γ : List (Ty S)}
    (st : Expr O' Γ (.prod GhostStT GhostStT))
    (b win : Expr O' Γ .bool)
    (epoch idx : Expr O' Γ (.prod .nat .nat))
    (tL : Expr O' Γ (.opt .nat))
    (trans : Expr O' Γ (.list (e2eRecTy ℓ)))
    (chall comp : Expr O' Γ (.list posTy))
    (maxAcc : Expr O' Γ (.prod (.tbl .nat) (.tbl .nat)))
    (leaks : Expr O' Γ (.list .nat))
    (corrs : Expr O' Γ (.list (.prod .bool .nat))) : Expr O' Γ (e2eGsTy ℓ) :=
  .pair st
    (.pair b
      (.pair win
        (.pair epoch
          (.pair idx
            (.pair tL
              (.pair trans
                (.pair chall
                  (.pair comp
                    (.pair maxAcc
                      (.pair leaks corrs))))))))))

def e2eInitGsE {Γ : List (Ty S)} (stA stB : Expr O' Γ GhostStT) (b : Expr O' Γ .bool) :
    Expr O' Γ (e2eGsTy ℓ) :=
  e2eGsMk (.pair stA stB) b (.bool false) (.pair (.nat 0) (.nat 0)) (.pair (.nat 0) (.nat 0))
    .none .nil .nil .nil (.pair (.tconst (.nat 0)) (.tconst (.nat 0))) .nil .nil

@[simp] theorem eval_e2eInitGsE {Key : Type}
    (sm : SMScheme Key (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (k : Key) {Γ : List (Ty S)}
    (stA stB : Expr O' Γ GhostStT) (b : Expr O' Γ .bool) (ρ : Env Γ)
    (hA : stA.eval ρ = sm.initA k) (hB : stB.eval ρ = sm.initB k) :
    (e2eInitGsE stA stB b).eval ρ = e2eGsEnc (CryptoGames.SM.initState sm k (b.eval ρ)) := by
  simp [e2eInitGsE, e2eGsMk, e2eGsEnc, CryptoGames.SM.initState, hA, hB, Expr.eval]

theorem cost_e2eInitGsE_le {Γ : List (Ty S)} (stA stB : Expr O' Γ GhostStT) (b : Expr O' Γ .bool) :
    (e2eInitGsE stA stB b).cost ≤ stA.cost + stB.cost + b.cost + 40 := by
  have hb0 : bits 0 = 1 := by decide
  simp only [e2eInitGsE, e2eGsMk, Expr.cost, hb0]
  omega

def e2eGsSetWin {Γ : List (Ty S)} (s : Expr O' Γ (e2eGsTy ℓ)) (w : Expr O' Γ .bool) :
    Expr O' Γ (e2eGsTy ℓ) :=
  .letE (.pair s w)
    (let s0 : Expr O' _ (e2eGsTy ℓ) := .fst .v0
     let w0 : Expr O' _ .bool := .snd .v0
     e2eGsMk (e2eGsSt s0) (e2eGsB s0) w0 (e2eGsEpoch s0) (e2eGsIdx s0) (e2eGsTL s0)
       (e2eGsTrans s0) (e2eGsChall s0) (e2eGsComp s0) (e2eGsMaxAcc s0)
       (e2eGsLeaks s0) (e2eGsCorrs s0))

@[simp] theorem eval_e2eGsSetWin {Γ : List (Ty S)} (s : Expr O' Γ (e2eGsTy ℓ))
    (w : Expr O' Γ .bool) (ρ : Env Γ)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (hs : s.eval ρ = e2eGsEnc st) :
    (e2eGsSetWin s w).eval ρ = e2eGsEnc { st with win := w.eval ρ } := by
  simp [e2eGsSetWin, e2eGsMk, e2eGsSt, e2eGsB, e2eGsEpoch, e2eGsIdx, e2eGsTL, e2eGsTrans,
    e2eGsChall, e2eGsComp, e2eGsMaxAcc, e2eGsLeaks, e2eGsCorrs, hs, e2eGsEnc, Expr.eval, Expr.v0]

theorem cost_e2eGsSetWin_le {Γ : List (Ty S)} (s : Expr O' Γ (e2eGsTy ℓ)) (w : Expr O' Γ .bool) :
    (e2eGsSetWin s w).cost ≤ s.cost + w.cost + 120 := by
  simp only [e2eGsSetWin, e2eGsMk, e2eGsSt, e2eGsB, e2eGsEpoch, e2eGsIdx, e2eGsTL, e2eGsTrans,
    e2eGsChall, e2eGsComp, e2eGsMaxAcc, e2eGsLeaks, e2eGsCorrs, Expr.cost, Expr.v0]
  omega

def e2eSafeChE {Γ : List (Ty S)} (Δ : ℕ) (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool) :
    Expr O' Γ .bool :=
  .letE (.pair s p)
    (healedByE (e2eGsTL (.fst .v0)) Δ (pGet (e2eGsEpoch (.fst .v0)) (.snd .v0)))

@[simp] theorem eval_e2eSafeChE {Γ : List (Ty S)} (Δ : ℕ) (s : Expr O' Γ (e2eGsTy ℓ))
    (p : Expr O' Γ .bool) (ρ : Env Γ)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (P : Party)
    (hs : s.eval ρ = e2eGsEnc st) (hp : p.eval ρ = partyEnc P) :
    (e2eSafeChE Δ s p).eval ρ = st.safeCh Δ P := by
  simp only [e2eSafeChE, Expr.eval, hs, hp, healedByE_eval]
  cases P <;> simp [GameState.safeCh, e2eGsTL, e2eGsEpoch, pGet, Expr.eval, Expr.v0,
    e2eGsEnc, partyEnc]

theorem cost_e2eSafeChE_le {Γ : List (Ty S)} (Δ : ℕ) (s : Expr O' Γ (e2eGsTy ℓ))
    (p : Expr O' Γ .bool) :
    (e2eSafeChE Δ s p).cost ≤ s.cost + p.cost + bits Δ + 40 := by
  simp only [e2eSafeChE, healedByE, leN, e2eGsTL, e2eGsEpoch, pGet, Expr.cost, Expr.v0, Expr.v1]
  omega

def e2eSafeInjE {Γ : List (Ty S)} (Δ : ℕ) (s : Expr O' Γ (e2eGsTy ℓ)) : Expr O' Γ .bool :=
  .letE s
    (healedByE (e2eGsTL .v0) Δ (minN (.fst (e2eGsEpoch .v0)) (.snd (e2eGsEpoch .v0))))

@[simp] theorem eval_e2eSafeInjE {Γ : List (Ty S)} (Δ : ℕ) (s : Expr O' Γ (e2eGsTy ℓ))
    (ρ : Env Γ) (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (hs : s.eval ρ = e2eGsEnc st) :
    (e2eSafeInjE Δ s).eval ρ = st.safeInj Δ := by
  simp only [e2eSafeInjE, Expr.eval, hs, healedByE_eval, minN_eval]
  simp [GameState.safeInj, e2eGsTL, e2eGsEpoch, Expr.eval, Expr.v0, e2eGsEnc]

theorem cost_e2eSafeInjE_le {Γ : List (Ty S)} (Δ : ℕ) (s : Expr O' Γ (e2eGsTy ℓ)) :
    (e2eSafeInjE Δ s).cost ≤ s.cost + bits Δ + 45 := by
  simp only [e2eSafeInjE, healedByE, leN, minN, e2eGsTL, e2eGsEpoch, Expr.cost, Expr.v0, Expr.v1]
  omega

def e2eLeakE {Γ : List (Ty S)} (s : Expr O' Γ (e2eGsTy ℓ)) (l : Expr O' Γ .nat) :
    Expr O' Γ (e2eGsTy ℓ) :=
  .letE (.pair s l)
    (let s0 : Expr O' _ (e2eGsTy ℓ) := .fst .v0
     let l0 : Expr O' _ .nat := .snd .v0
     .letE (maxOptE (e2eGsTL s0) l0)
       (let m : Expr O' _ .nat := .v0
        let s1 : Expr O' _ (e2eGsTy ℓ) := .fst .v1
        e2eGsMk (e2eGsSt s1) (e2eGsB s1) (e2eGsWin s1) (e2eGsEpoch s1) (e2eGsIdx s1)
          (.some m) (e2eGsTrans s1) (e2eGsChall s1) (e2eGsComp s1) (e2eGsMaxAcc s1)
          (.cons m (e2eGsLeaks s1)) (e2eGsCorrs s1)))

@[simp] theorem eval_e2eLeakE {Γ : List (Ty S)} (s : Expr O' Γ (e2eGsTy ℓ)) (l : Expr O' Γ .nat)
    (ρ : Env Γ) (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (hs : s.eval ρ = e2eGsEnc st) :
    (e2eLeakE s l).eval ρ = e2eGsEnc (st.leak (l.eval ρ)) := by
  simp only [e2eLeakE, e2eGsMk, Expr.eval, hs, maxOptE_eval]
  simp [GameState.leak, e2eGsSt, e2eGsB, e2eGsWin, e2eGsEpoch, e2eGsIdx, e2eGsTL, e2eGsTrans,
    e2eGsChall, e2eGsComp, e2eGsMaxAcc, e2eGsLeaks, e2eGsCorrs, Expr.eval, Expr.v0, Expr.v1,
    e2eGsEnc]

theorem cost_e2eLeakE_le {Γ : List (Ty S)} (s : Expr O' Γ (e2eGsTy ℓ)) (l : Expr O' Γ .nat) :
    (e2eLeakE s l).cost ≤ s.cost + l.cost + 155 := by
  simp only [e2eLeakE, maxOptE, maxN, leN, e2eGsMk, e2eGsSt, e2eGsB, e2eGsWin, e2eGsEpoch,
    e2eGsIdx, e2eGsTL, e2eGsTrans, e2eGsChall, e2eGsComp, e2eGsMaxAcc, e2eGsLeaks, e2eGsCorrs,
    Expr.cost, Expr.v0, Expr.v1]
  omega

def e2eEpMgmtE {Γ : List (Ty S)} (Δ qep : ℕ) (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool)
    (bad : Expr O' Γ .bool) : Expr O' Γ (.opt (e2eGsTy ℓ)) :=
  .letE (.pair s (.pair p bad))
    (let s0 : Expr O' _ (e2eGsTy ℓ) := .fst .v0
     let p0 : Expr O' _ .bool := .fst (.snd .v0)
     let bad0 : Expr O' _ .bool := .snd (.snd .v0)
     let epP : Expr O' _ .nat := pGet (e2eGsEpoch s0) p0
     let epNext : Expr O' _ .nat := .add epP (.nat 1)
     .ite (sendsInE p0 epNext)
       (.ite (.lt (.nat qep) epNext)
         .none
         (.letE (.ite (.and bad0 (.not (e2eSafeChE Δ s0 p0))) (e2eLeakE s0 epNext) s0)
           (let s1 : Expr O' _ (e2eGsTy ℓ) := .v0
            let p1 : Expr O' _ .bool := .fst (.snd .v1)
            let ep1 : Expr O' _ .nat := .add (pGet (e2eGsEpoch s1) p1) (.nat 1)
            .some (e2eGsMk (e2eGsSt s1) (e2eGsB s1) (e2eGsWin s1)
              (pSet (e2eGsEpoch s1) p1 ep1)
              (pSet (e2eGsIdx s1) p1 (.nat 0))
              (e2eGsTL s1) (e2eGsTrans s1) (e2eGsChall s1) (e2eGsComp s1)
              (e2eGsMaxAcc s1) (e2eGsLeaks s1) (e2eGsCorrs s1)))))
       (.ite (.lt (.nat qep) epP)
         .none
         (.some s0)))

@[simp] theorem eval_e2eEpMgmtE {Γ : List (Ty S)} (Δ qep : ℕ) (s : Expr O' Γ (e2eGsTy ℓ))
    (p : Expr O' Γ .bool) (bad : Expr O' Γ .bool) (ρ : Env Γ)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (P : Party)
    (hs : s.eval ρ = e2eGsEnc st) (hp : p.eval ρ = partyEnc P) :
    (e2eEpMgmtE Δ qep s p bad).eval ρ = (st.epMgmt Δ qep P (bad.eval ρ)).map e2eGsEnc := by
  unfold e2eEpMgmtE GameState.epMgmt
  rw [letE_eval]
  have h0 : (Expr.pair s (.pair p bad)).eval ρ = (e2eGsEnc st, (partyEnc P, bad.eval ρ)) := by
    simp [Expr.eval, hs, hp]
  rw [h0]; clear h0
  set ρ₁ := Env.cons (t := .prod (e2eGsTy ℓ) (.prod .bool .bool))
    (e2eGsEnc st, (partyEnc P, bad.eval ρ)) ρ
  rw [ite_eval]
  have hSends : (sendsInE (.fst (.snd (Expr.v0 (O := O'))))
      (.add (pGet (e2eGsEpoch (.fst (Expr.v0 (O := O')))) (.fst (.snd (Expr.v0 (O := O')))))
        (.nat 1))).eval ρ₁ = P.sendsIn (st.epoch P + 1) := by
    rw [sendsInE_eval _ _ ρ₁ P rfl]
    congr 1
    cases P <;> simp [ρ₁, pGet, e2eGsEpoch, e2eGsEnc, partyEnc, Expr.eval, Expr.v0]
  rw [hSends]
  by_cases h1 : P.sendsIn (st.epoch P + 1)
  · simp only [h1, ↓reduceIte]
    rw [ite_eval]
    have hlt1 : (Expr.lt (.nat qep) (.add (pGet (e2eGsEpoch (.fst (Expr.v0 (O := O'))))
        (.fst (.snd (Expr.v0 (O := O'))))) (.nat 1))).eval ρ₁ =
        decide (qep < st.epoch P + 1) := by
      cases P <;> simp [ρ₁, pGet, e2eGsEpoch, e2eGsEnc, partyEnc, Expr.eval, Expr.v0]
    rw [hlt1]
    by_cases h2 : qep < st.epoch P + 1
    · simp [h2, Expr.eval]
    · simp only [h2, decide_false, Bool.false_eq_true, ↓reduceIte, Option.map_some]
      rw [letE_eval, ite_eval]
      have hCond : (Expr.and (.snd (.snd (Expr.v0 (O := O'))))
          (.not (e2eSafeChE Δ (.fst (Expr.v0 (O := O')))
            (.fst (.snd (Expr.v0 (O := O'))))))).eval ρ₁ =
          (bad.eval ρ && !(st.safeCh Δ P)) := by
        have hsafe := eval_e2eSafeChE Δ (.fst (Expr.v0 (O := O')))
          (.fst (.snd (Expr.v0 (O := O')))) ρ₁ st P rfl rfl
        simp only [Expr.eval, hsafe]
        rfl
      have hLeak : (e2eLeakE (.fst (Expr.v0 (O := O')))
          (.add (pGet (e2eGsEpoch (.fst (Expr.v0 (O := O')))) (.fst (.snd (Expr.v0 (O := O')))))
            (.nat 1))).eval ρ₁ = e2eGsEnc (st.leak (st.epoch P + 1)) := by
        rw [eval_e2eLeakE (.fst (Expr.v0 (O := O'))) _ ρ₁ st rfl]
        congr 2
        cases P <;> simp [ρ₁, pGet, e2eGsEpoch, e2eGsEnc, partyEnc, Expr.eval, Expr.v0]
      have hBase : (Expr.fst (Expr.v0 (O := O'))).eval ρ₁ = e2eGsEnc st := rfl
      rw [hCond, hLeak, hBase]
      set st₁ := if (bad.eval ρ && !(st.safeCh Δ P)) = true then st.leak (st.epoch P + 1) else st
      have hst₁ : (if (bad.eval ρ && !(st.safeCh Δ P)) = true
          then e2eGsEnc (st.leak (st.epoch P + 1))
          else e2eGsEnc st) = e2eGsEnc st₁ := by
        dsimp only [st₁]; split_ifs <;> rfl
      rw [hst₁]
      cases P <;>
        simp [ρ₁, e2eGsMk, e2eGsSt, e2eGsB, e2eGsWin, e2eGsEpoch, e2eGsIdx, e2eGsTL, e2eGsTrans,
          e2eGsChall, e2eGsComp, e2eGsMaxAcc, e2eGsLeaks, e2eGsCorrs, pGet, pSet, e2eGsEnc,
          partyEnc, Function.update, Expr.eval, Expr.v0, Expr.v1]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    rw [ite_eval]
    have hlt2 : (Expr.lt (.nat qep) (pGet (e2eGsEpoch (.fst (Expr.v0 (O := O'))))
        (.fst (.snd (Expr.v0 (O := O')))))).eval ρ₁ = decide (qep < st.epoch P) := by
      cases P <;> simp [ρ₁, pGet, e2eGsEpoch, e2eGsEnc, partyEnc, Expr.eval, Expr.v0]
    rw [hlt2]
    by_cases h2 : qep < st.epoch P <;> simp [ρ₁, h2, Expr.eval, Expr.v0]

theorem cost_e2eEpMgmtE_le {Γ : List (Ty S)} (Δ qep : ℕ) (s : Expr O' Γ (e2eGsTy ℓ))
    (p : Expr O' Γ .bool) (bad : Expr O' Γ .bool) :
    (e2eEpMgmtE Δ qep s p bad).cost ≤
      s.cost + p.cost + bad.cost + bits Δ + bits qep + 460 := by
  let t0 : Ty S := .prod (e2eGsTy ℓ) (.prod .bool .bool)
  have hsafe := cost_e2eSafeChE_le (ℓ := ℓ) (O' := O') Δ
    (.fst .v0 : Expr O' (t0 :: Γ) (e2eGsTy ℓ)) (.fst (.snd .v0))
  have hleak := cost_e2eLeakE_le (ℓ := ℓ) (O' := O')
    (.fst .v0 : Expr O' (t0 :: Γ) (e2eGsTy ℓ))
    (.add (pGet (e2eGsEpoch (.fst .v0)) (.fst (.snd .v0))) (.nat 1))
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  have hb2 : bits 2 = 2 := by decide
  simp only [e2eEpMgmtE, sendsInE, pGet, pSet, e2eGsMk, e2eGsSt, e2eGsB, e2eGsWin,
    e2eGsEpoch, e2eGsIdx, e2eGsTL, e2eGsTrans, e2eGsChall, e2eGsComp, e2eGsMaxAcc, e2eGsLeaks,
    e2eGsCorrs, Expr.cost, Expr.v0, Expr.v1, hb0, hb1, hb2] at hsafe hleak ⊢
  omega

def e2eCompContainsE {Γ : List (Ty S)} (q : ℕ) (s : Expr O' Γ (e2eGsTy ℓ))
    (pos : Expr O' Γ posTy) : Expr O' Γ .bool :=
  .letE (.pair s pos)
    (.anyB q (e2eGsComp (.fst .v0)) (posEq .v0 (.snd .v1)))

@[simp] theorem eval_e2eCompContainsE {Γ : List (Ty S)} (q : ℕ) (s : Expr O' Γ (e2eGsTy ℓ))
    (pos : Expr O' Γ posTy) (ρ : Env Γ)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (p : Pos)
    (hcomp : (dedupComp st.comp).length ≤ q)
    (hs : s.eval ρ = e2eGsEnc st) (hp : pos.eval ρ = posEnc p) :
    (e2eCompContainsE q s pos).eval ρ = st.comp.contains p := by
  have htake : (((dedupComp st.comp).map posEnc).take q) = (dedupComp st.comp).map posEnc :=
    List.take_of_length_le (by simpa using hcomp)
  unfold e2eCompContainsE
  rw [letE_eval]
  have hp0 : (Expr.pair s pos).eval ρ = (e2eGsEnc st, posEnc p) := by
    simp [Expr.eval, hs, hp]
  rw [hp0]; clear hp0
  set ρ₁ := Env.cons (t := .prod (e2eGsTy ℓ) posTy) (e2eGsEnc st, posEnc p) ρ
  dsimp only [Expr.eval]
  have hg : (e2eGsComp (.fst (Expr.v0 (O := O')))).eval ρ₁ = (dedupComp st.comp).map posEnc := rfl
  rw [hg, htake, any_map_eq, ← dedupComp_contains, ← any_beq_eq_contains]
  congr 1
  funext x
  simp [ρ₁, posEq_eval, CryptoGames.SM.posDec_posEnc, Expr.eval, Expr.v0, Expr.v1]

theorem cost_e2eCompContainsE_le {Γ : List (Ty S)} (q : ℕ) (s : Expr O' Γ (e2eGsTy ℓ))
    (pos : Expr O' Γ posTy) :
    (e2eCompContainsE q s pos).cost ≤ s.cost + pos.cost + 45 * q + 15 := by
  have hm34 : max (1 + 1 + 1) (1 + 1 + 1 + 1) = 4 := rfl
  simp only [e2eCompContainsE, e2eGsComp, posEq, posSender, posEpoch, posIdx, boolEq, Expr.cost,
    Expr.v0, Expr.v1, hm34]
  omega

def e2eChallContainsE {Γ : List (Ty S)} (q : ℕ) (s : Expr O' Γ (e2eGsTy ℓ))
    (pos : Expr O' Γ posTy) : Expr O' Γ .bool :=
  .letE (.pair s pos)
    (.anyB q (e2eGsChall (.fst .v0)) (posEq .v0 (.snd .v1)))

@[simp] theorem eval_e2eChallContainsE {Γ : List (Ty S)} (q : ℕ) (s : Expr O' Γ (e2eGsTy ℓ))
    (pos : Expr O' Γ posTy) (ρ : Env Γ)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (p : Pos)
    (hchall : st.chall.length ≤ q)
    (hs : s.eval ρ = e2eGsEnc st) (hp : pos.eval ρ = posEnc p) :
    (e2eChallContainsE q s pos).eval ρ = st.chall.contains p := by
  have htake : ((st.chall.map posEnc).take q) = st.chall.map posEnc :=
    List.take_of_length_le (by simpa using hchall)
  unfold e2eChallContainsE
  rw [letE_eval]
  have hp0 : (Expr.pair s pos).eval ρ = (e2eGsEnc st, posEnc p) := by
    simp [Expr.eval, hs, hp]
  rw [hp0]; clear hp0
  set ρ₁ := Env.cons (t := .prod (e2eGsTy ℓ) posTy) (e2eGsEnc st, posEnc p) ρ
  dsimp only [Expr.eval]
  have hg : (e2eGsChall (.fst (Expr.v0 (O := O')))).eval ρ₁ = st.chall.map posEnc := rfl
  rw [hg, htake, any_map_eq, ← any_beq_eq_contains]
  congr 1
  funext x
  simp [ρ₁, posEq_eval, CryptoGames.SM.posDec_posEnc, Expr.eval, Expr.v0, Expr.v1]

theorem cost_e2eChallContainsE_le {Γ : List (Ty S)} (q : ℕ) (s : Expr O' Γ (e2eGsTy ℓ))
    (pos : Expr O' Γ posTy) :
    (e2eChallContainsE q s pos).cost ≤ s.cost + pos.cost + 45 * q + 15 := by
  have hm34 : max (1 + 1 + 1) (1 + 1 + 1 + 1) = 4 := rfl
  simp only [e2eChallContainsE, e2eGsChall, posEq, posSender, posEpoch, posIdx, boolEq, Expr.cost,
    Expr.v0, Expr.v1, hm34]
  omega

private theorem foldrB_eval {α β : Ty S} {Γ : List (Ty S)} (n : ℕ)
    (xs : Expr O' Γ (.list α)) (init : Expr O' Γ β) (step : Expr O' (α :: β :: Γ) β)
    (ρ : Env Γ) :
    (Expr.foldrB n xs init step).eval ρ =
      ((xs.eval ρ).take n).foldr (fun x acc => step.eval (.cons x (.cons acc ρ))) (init.eval ρ) :=
  rfl

private theorem cons_eval {α : Ty S} {Γ : List (Ty S)} (h : Expr O' Γ α)
    (t : Expr O' Γ (.list α)) (ρ : Env Γ) :
    (Expr.cons h t).eval ρ = h.eval ρ :: t.eval ρ :=
  rfl

private theorem and_eval {Γ : List (Ty S)} (a b : Expr O' Γ .bool) (ρ : Env Γ) :
    (Expr.and a b).eval ρ = (a.eval ρ && b.eval ρ) :=
  rfl

private theorem not_eval {Γ : List (Ty S)} (a : Expr O' Γ .bool) (ρ : Env Γ) :
    (Expr.not a).eval ρ = !a.eval ρ :=
  rfl

@[simp] private theorem party_beq_AA : (Party.A == Party.A) = true := rfl
@[simp] private theorem party_beq_BB : (Party.B == Party.B) = true := rfl
@[simp] private theorem party_beq_AB : (Party.A == Party.B) = false := rfl
@[simp] private theorem party_beq_BA : (Party.B == Party.A) = false := rfl

private theorem nat_beq_eq_decide (a b : ℕ) : (a == b) = decide (a = b) := by
  cases h : (a == b) <;> simp_all [beq_iff_eq]

private theorem pos_beq_eq_decide (x y : Pos) : (x == y) = decide (x = y) := by
  rcases x with ⟨sx, ex, ix⟩
  rcases y with ⟨sy, ey, iy⟩
  cases sx <;> cases sy <;> simp [BEq.beq]

/-- Linear `O(q)` `SM.GameState.record s Δ P st' ⟨pos, msg, ct⟩ isChall` over `e2eGsTy ℓ`,
maintaining both `dedupComp` on `comp` and cached compromise flags on `trans`. -/
def e2eRecordE {Γ : List (Ty S)} (q Δ : ℕ) (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool)
    (st' : Expr O' Γ GhostStT) (pos : Expr O' Γ posTy) (msg : Expr O' Γ PlainT)
    (ct : Expr O' Γ (B 32)) (isChall : Expr O' Γ .bool) : Expr O' Γ (e2eGsTy ℓ) :=
  .letE (.pair s (.pair p (.pair st' (.pair pos (.pair msg (.pair ct isChall))))))
    (.letE (.pair (e2eSafeChE Δ (.fst .v0) (.fst (.snd .v0)))
                  (e2eCompContainsE q (.fst .v0) (.fst (.snd (.snd (.snd .v0))))))
      (let safe0 : Expr O' _ .bool := .fst .v0
       let inComp0 : Expr O' _ .bool := .snd .v0
       let top := .v1
       let s0 : Expr O' _ (e2eGsTy ℓ) := .fst top
       let p0 : Expr O' _ .bool := .fst (.snd top)
       let st0 : Expr O' _ GhostStT := .fst (.snd (.snd top))
       let pos0 : Expr O' _ posTy := .fst (.snd (.snd (.snd top)))
       let msg0 : Expr O' _ PlainT := .fst (.snd (.snd (.snd (.snd top))))
       let ct0 : Expr O' _ (B 32) := .fst (.snd (.snd (.snd (.snd (.snd top)))))
       let ch0 : Expr O' _ .bool := .snd (.snd (.snd (.snd (.snd (.snd top)))))
       let headRec : Expr O' _ (e2eRecTy ℓ) :=
         e2eRecMk pos0 msg0 ct0 (orE (.not safe0) inComp0)
       let tailTrans : Expr O' _ (.list (e2eRecTy ℓ)) :=
         .mapB q (e2eGsTrans s0)
           (let rElem : Expr O' _ (e2eRecTy ℓ) := .v0
            let safe1 : Expr O' _ .bool := .fst .v1
            let pos1 : Expr O' _ posTy := .fst (.snd (.snd (.snd .v2)))
            e2eRecMk (e2eRecPos rElem) (e2eRecMsg rElem) (e2eRecCt rElem)
              (orE (.and (.not safe1) (posEq (e2eRecPos rElem) pos1)) (e2eRecComp rElem)))
       let chall' : Expr O' _ (.list posTy) :=
         .ite ch0 (.cons pos0 (e2eGsChall s0)) (e2eGsChall s0)
       let comp' : Expr O' _ (.list posTy) :=
         .ite (orE safe0 inComp0) (e2eGsComp s0) (.cons pos0 (e2eGsComp s0))
       e2eGsMk
         (pSet (e2eGsSt s0) p0 st0)
         (e2eGsB s0) (e2eGsWin s0) (e2eGsEpoch s0)
         (pSet (e2eGsIdx s0) p0 (posIdx pos0))
         (e2eGsTL s0)
         (.cons headRec tailTrans)
         chall'
         comp'
         (e2eGsMaxAcc s0) (e2eGsLeaks s0) (e2eGsCorrs s0)))

private theorem contains_record_comp (safe : Bool) (p0 x : Pos) (comp : List Pos) :
    (if safe then comp else p0 :: comp).contains x =
      ((!safe && (x == p0)) || comp.contains x) := by
  cases safe <;> simp [pos_beq_eq_decide]

private theorem dedupComp_record_map (safe : Bool) (p0 : Pos) (comp : List Pos) :
    (dedupComp (if safe then comp else p0 :: comp)).map posEnc =
      if safe || comp.contains p0 then (dedupComp comp).map posEnc
      else posEnc p0 :: (dedupComp comp).map posEnc := by
  cases safe
  · change (dedupComp (p0 :: comp)).map posEnc =
      if comp.contains p0 then (dedupComp comp).map posEnc
      else posEnc p0 :: (dedupComp comp).map posEnc
    dsimp only [dedupComp]
    rw [dedupComp_contains]
    cases comp.contains p0 <;> rfl
  · simp

@[simp] theorem eval_e2eRecordE {Γ : List (Ty S)} (q Δ : ℕ) (s : Expr O' Γ (e2eGsTy ℓ))
    (p : Expr O' Γ .bool) (st' : Expr O' Γ GhostStT) (pos : Expr O' Γ posTy)
    (msg : Expr O' Γ PlainT) (ct : Expr O' Γ (B 32)) (isChall : Expr O' Γ .bool) (ρ : Env Γ)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (P : Party) (p0 : Pos)
    (htrans : st.trans.length ≤ q) (hcomp : (dedupComp st.comp).length ≤ q)
    (hs : s.eval ρ = e2eGsEnc st) (hp : p.eval ρ = partyEnc P) (hpos : pos.eval ρ = posEnc p0) :
    (e2eRecordE q Δ s p st' pos msg ct isChall).eval ρ =
      e2eGsEnc (st.record Δ P (st'.eval ρ) ⟨p0, msg.eval ρ, ct.eval ρ⟩ (isChall.eval ρ)) := by
  unfold e2eRecordE
  rw [letE_eval]
  let tTop : Ty S := .prod (e2eGsTy ℓ)
    (.prod .bool (.prod GhostStT (.prod posTy (.prod PlainT (.prod (B 32) .bool)))))
  set tupVal : tTop.denote := (e2eGsEnc st, (partyEnc P, (st'.eval ρ, (posEnc p0,
    (msg.eval ρ, (ct.eval ρ, isChall.eval ρ))))))
  have htup : (Expr.pair s (.pair p (.pair st' (.pair pos (.pair msg (.pair ct isChall)))))).eval ρ =
      tupVal := by
    simp [tupVal, Expr.eval, hs, hp, hpos]
  rw [htup]; clear htup
  set ρ₁ := Env.cons (t := tTop) tupVal ρ
  rw [letE_eval]
  have hsafe : (e2eSafeChE Δ (.fst (Expr.v0 (O := O'))) (.fst (.snd (Expr.v0 (O := O'))))).eval ρ₁ =
      st.safeCh Δ P :=
    eval_e2eSafeChE Δ (.fst .v0) (.fst (.snd .v0)) ρ₁ st P rfl rfl
  have hinComp : (e2eCompContainsE q (.fst (Expr.v0 (O := O')))
      (.fst (.snd (.snd (.snd (Expr.v0 (O := O'))))))).eval ρ₁ = st.comp.contains p0 :=
    eval_e2eCompContainsE q (.fst .v0) (.fst (.snd (.snd (.snd .v0)))) ρ₁ st p0 hcomp rfl rfl
  have hp2 : (Expr.pair (e2eSafeChE Δ (.fst (Expr.v0 (O := O'))) (.fst (.snd (Expr.v0 (O := O')))))
      (e2eCompContainsE q (.fst (Expr.v0 (O := O')))
        (.fst (.snd (.snd (.snd (Expr.v0 (O := O')))))))).eval ρ₁ =
      (st.safeCh Δ P, st.comp.contains p0) := by
    simp [Expr.eval, hsafe, hinComp]
  rw [hp2]; clear hp2
  set ρ₂ := Env.cons (t := .prod .bool .bool) (st.safeCh Δ P, st.comp.contains p0) ρ₁
  have htake : ((st.trans.map (e2eRecEncWith st.comp)).take q) =
      st.trans.map (e2eRecEncWith st.comp) :=
    List.take_of_length_le (by simpa using htrans)
  have hmap_tail :
      (Expr.mapB q (e2eGsTrans (.fst (Expr.v1 (O := O'))))
        (e2eRecMk (e2eRecPos .v0) (e2eRecMsg .v0) (e2eRecCt .v0)
          (orE (.and (.not (.fst .v1)) (posEq (e2eRecPos .v0) (.fst (.snd (.snd (.snd .v2))))))
            (e2eRecComp .v0)))).eval ρ₂ =
      st.trans.map (e2eRecEncWith (if st.safeCh Δ P then st.comp else p0 :: st.comp)) := by
    dsimp only [Expr.eval]
    have hgs : (e2eGsTrans (.fst (Expr.v1 (O := O')))).eval ρ₂ =
        st.trans.map (e2eRecEncWith st.comp) := rfl
    rw [hgs, htake, List.map_map]
    refine List.map_congr_left fun r _ => ?_
    simp only [Function.comp_apply, e2eRecMk, e2eRecPos, e2eRecMsg, e2eRecCt, e2eRecComp,
      orE_eval, posEq_eval, Expr.eval, Expr.v0, Expr.v1, Expr.v2, Env.get, ρ₂, ρ₁, tupVal,
      e2eRecEncWith, CryptoGames.SM.posDec_posEnc, contains_record_comp]
  have hhead_flag :
      ((!st.safeCh Δ P) || st.comp.contains p0) =
        (if st.safeCh Δ P then st.comp else p0 :: st.comp).contains p0 := by
    rw [contains_record_comp]
    have hp0_eq : (p0 == p0) = true := by
      rw [pos_beq_eq_decide]
      simp
    rw [hp0_eq, Bool.and_true]
  have hstUpd :
      (pSet (e2eGsSt (.fst (Expr.v1 (O := O')))) (.fst (.snd (Expr.v1 (O := O'))))
        (.fst (.snd (.snd (Expr.v1 (O := O')))))).eval ρ₂ =
      (Function.update st.st P (st'.eval ρ) .A, Function.update st.st P (st'.eval ρ) .B) := by
    rw [pSet_eval _ _ _ ρ₂ st.st P rfl rfl]
    rfl
  have hidxUpd :
      (pSet (e2eGsIdx (.fst (Expr.v1 (O := O')))) (.fst (.snd (Expr.v1 (O := O'))))
        (posIdx (.fst (.snd (.snd (.snd (Expr.v1 (O := O')))))))).eval ρ₂ =
      (Function.update st.idx P p0.idx .A, Function.update st.idx P p0.idx .B) := by
    rw [pSet_eval _ _ _ ρ₂ st.idx P rfl rfl]
    rfl
  simp only [e2eGsMk, pair_eval, cons_eval, hstUpd, hidxUpd, hmap_tail]
  simp only [Expr.eval, orE_eval, e2eRecMk, ρ₂, ρ₁, tupVal, e2eGsB, e2eGsWin, e2eGsEpoch,
    e2eGsTL, e2eGsChall, e2eGsComp, e2eGsMaxAcc, e2eGsLeaks, e2eGsCorrs, Expr.v0, Expr.v1,
    Env.get, e2eGsEnc, GameState.record]
  rw [hhead_flag, ← dedupComp_record_map (st.safeCh Δ P) p0 st.comp]
  cases isChall.eval ρ <;> rfl

theorem cost_e2eRecordE_le {Γ : List (Ty S)} (q Δ : ℕ) (s : Expr O' Γ (e2eGsTy ℓ))
    (p : Expr O' Γ .bool) (st' : Expr O' Γ GhostStT) (pos : Expr O' Γ posTy)
    (msg : Expr O' Γ PlainT) (ct : Expr O' Γ (B 32)) (isChall : Expr O' Γ .bool) :
    (e2eRecordE q Δ s p st' pos msg ct isChall).cost ≤
      s.cost + p.cost + st'.cost + pos.cost + msg.cost + ct.cost + isChall.cost +
        bits Δ + 135 * q + 380 := by
  let tTop : Ty S := .prod (e2eGsTy ℓ)
    (.prod .bool (.prod GhostStT (.prod posTy (.prod PlainT (.prod (B 32) .bool)))))
  have hm34 : max (1 + 1 + 1) (1 + 1 + 1 + 1) = 4 := rfl
  have hm14 : max 1 (1 + 1 + 1 + 1) = 4 := rfl
  have hsafe := cost_e2eSafeChE_le (ℓ := ℓ) (O' := O') Δ
    (.fst .v0 : Expr O' (tTop :: Γ) (e2eGsTy ℓ)) (.fst (.snd .v0))
  have hcomp := cost_e2eCompContainsE_le (ℓ := ℓ) (O' := O') q
    (.fst .v0 : Expr O' (tTop :: Γ) (e2eGsTy ℓ)) (.fst (.snd (.snd (.snd .v0))))
  simp only [e2eRecordE, e2eGsMk, e2eRecMk, e2eRecPos, e2eRecMsg, e2eRecCt, e2eRecComp,
    e2eGsSt, e2eGsB, e2eGsWin, e2eGsEpoch, e2eGsIdx, e2eGsTL, e2eGsTrans, e2eGsChall, e2eGsComp,
    e2eGsMaxAcc, e2eGsLeaks, e2eGsCorrs, pSet, posEq, posSender, posEpoch, posIdx, boolEq, orE,
    Expr.cost, Expr.v0, Expr.v1, Expr.v2, hm34, hm14] at hsafe hcomp ⊢
  omega

def e2eDeleteE {Γ : List (Ty S)} (q : ℕ) (s : Expr O' Γ (e2eGsTy ℓ)) (pos : Expr O' Γ posTy) :
    Expr O' Γ (e2eGsTy ℓ) :=
  .letE (.pair s pos)
    (let s0 : Expr O' (.prod (e2eGsTy ℓ) posTy :: Γ) (e2eGsTy ℓ) := .fst .v0
     let trans' : Expr O' _ (.list (e2eRecTy ℓ)) :=
       .foldrB q (e2eGsTrans s0) .nil
         (.ite (.not (posEq (e2eRecPos .v0) (.snd .v2))) (.cons .v0 .v1) .v1)
     let chall' : Expr O' _ (.list posTy) :=
       .foldrB q (e2eGsChall s0) .nil
         (.ite (.not (posEq .v0 (.snd .v2))) (.cons .v0 .v1) .v1)
     let comp' : Expr O' _ (.list posTy) :=
       .foldrB q (e2eGsComp s0) .nil
         (.ite (.not (posEq .v0 (.snd .v2))) (.cons .v0 .v1) .v1)
     e2eGsMk (e2eGsSt s0) (e2eGsB s0) (e2eGsWin s0) (e2eGsEpoch s0) (e2eGsIdx s0) (e2eGsTL s0)
       trans' chall' comp' (e2eGsMaxAcc s0) (e2eGsLeaks s0) (e2eGsCorrs s0))

private theorem contains_filter_ne_of_ne (comp : List Pos) {x p0 : Pos} (hne : (x != p0) = true) :
    (comp.filter (· != p0)).contains x = comp.contains x := by
  simp only [List.contains_eq_mem, List.mem_filter]
  by_cases hx : x ∈ comp
  · simp [hx, hne]
  · simp [hx]

@[simp] theorem eval_e2eDeleteE {Γ : List (Ty S)} (q : ℕ) (s : Expr O' Γ (e2eGsTy ℓ))
    (pos : Expr O' Γ posTy) (ρ : Env Γ)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (p0 : Pos)
    (hbnd : SmListBounded q st)
    (hs : s.eval ρ = e2eGsEnc st) (hp : pos.eval ρ = posEnc p0) :
    (e2eDeleteE q s pos).eval ρ = e2eGsEnc (st.delete p0) := by
  have htTrans : ((st.trans.map (e2eRecEncWith st.comp)).take q) =
      st.trans.map (e2eRecEncWith st.comp) :=
    List.take_of_length_le (by simpa using hbnd.trans_le)
  have htChall : ((st.chall.map posEnc).take q) = st.chall.map posEnc :=
    List.take_of_length_le (by simpa using hbnd.chall_le)
  have htComp : (((dedupComp st.comp).map posEnc).take q) = (dedupComp st.comp).map posEnc :=
    List.take_of_length_le (by simpa using hbnd.dedupComp_le)
  unfold e2eDeleteE
  rw [letE_eval]
  have hp0 : (Expr.pair s pos).eval ρ = (e2eGsEnc st, posEnc p0) := by
    simp [Expr.eval, hs, hp]
  rw [hp0]; clear hp0
  set ρ₁ := Env.cons (t := .prod (e2eGsTy ℓ) posTy) (e2eGsEnc st, posEnc p0) ρ
  have hnilT : (Expr.nil : Expr O' _ (.list (e2eRecTy ℓ))).eval ρ₁ = [] := rfl
  have hnilP : (Expr.nil : Expr O' _ (.list posTy)).eval ρ₁ = [] := rfl
  have hTransEq :
      (Expr.foldrB q (e2eGsTrans (.fst (Expr.v0 (O := O')))) .nil
        (.ite (.not (posEq (e2eRecPos .v0) (.snd .v2))) (.cons .v0 .v1) .v1)).eval ρ₁ =
      (st.delete p0).trans.map (e2eRecEncWith (st.delete p0).comp) := by
    rw [foldrB_eval]
    have hg : (e2eGsTrans (.fst (Expr.v0 (O := O')))).eval ρ₁ =
        st.trans.map (e2eRecEncWith st.comp) := rfl
    rw [hg, htTrans, hnilT]
    have hf :
        (st.trans.map (e2eRecEncWith st.comp)).foldr
          (fun x acc =>
            (Expr.ite (O := O') (.not (posEq (e2eRecPos .v0) (.snd .v2))) (.cons .v0 .v1) .v1).eval
              (.cons x (.cons acc ρ₁))) [] =
        (st.trans.map (e2eRecEncWith st.comp)).foldr
          (fun x acc => if !(posDec x.1 == p0) then x :: acc else acc) [] := by
      congr 1
      funext x acc
      simp [ρ₁, e2eRecPos, posEq_eval, Expr.eval, Expr.v0, Expr.v1, Expr.v2]
    rw [hf, foldr_filter_map]
    dsimp only [GameState.delete]
    have hflt :
        st.trans.filter (fun r => !(posDec (e2eRecEncWith st.comp r).1 == p0)) =
          st.trans.filter (fun r => r.pos != p0) := by
      refine List.filter_congr fun r _ => ?_
      simp [e2eRecEncWith, bne]
    rw [hflt]
    refine List.map_congr_left fun r hr => ?_
    have hne : (r.pos != p0) = true := (List.mem_filter.mp hr).2
    dsimp only [e2eRecEncWith]
    rw [contains_filter_ne_of_ne st.comp hne]
  have hChallEq :
      (Expr.foldrB q (e2eGsChall (.fst (Expr.v0 (O := O')))) .nil
        (.ite (.not (posEq .v0 (.snd .v2))) (.cons .v0 .v1) .v1)).eval ρ₁ =
      (st.delete p0).chall.map posEnc := by
    rw [foldrB_eval]
    have hg : (e2eGsChall (.fst (Expr.v0 (O := O')))).eval ρ₁ = st.chall.map posEnc := rfl
    rw [hg, htChall, hnilP]
    have hf :
        (st.chall.map posEnc).foldr
          (fun x acc =>
            (Expr.ite (O := O') (.not (posEq .v0 (.snd .v2))) (.cons .v0 .v1) .v1).eval
              (.cons x (.cons acc ρ₁))) [] =
        (st.chall.map posEnc).foldr
          (fun x acc => if !(posDec x == p0) then x :: acc else acc) [] := by
      congr 1
      funext x acc
      simp [ρ₁, posEq_eval, Expr.eval, Expr.v0, Expr.v1, Expr.v2]
    rw [hf, foldr_filter_map]
    dsimp only [GameState.delete]
    congr 1
    refine List.filter_congr fun x _ => ?_
    simp [bne]
  have hCompEq :
      (Expr.foldrB q (e2eGsComp (.fst (Expr.v0 (O := O')))) .nil
        (.ite (.not (posEq .v0 (.snd .v2))) (.cons .v0 .v1) .v1)).eval ρ₁ =
      (dedupComp (st.delete p0).comp).map posEnc := by
    rw [foldrB_eval]
    have hg : (e2eGsComp (.fst (Expr.v0 (O := O')))).eval ρ₁ =
        (dedupComp st.comp).map posEnc := rfl
    rw [hg, htComp, hnilP]
    have hf :
        ((dedupComp st.comp).map posEnc).foldr
          (fun x acc =>
            (Expr.ite (O := O') (.not (posEq .v0 (.snd .v2))) (.cons .v0 .v1) .v1).eval
              (.cons x (.cons acc ρ₁))) [] =
        ((dedupComp st.comp).map posEnc).foldr
          (fun x acc => if !(posDec x == p0) then x :: acc else acc) [] := by
      congr 1
      funext x acc
      simp [ρ₁, posEq_eval, Expr.eval, Expr.v0, Expr.v1, Expr.v2]
    rw [hf, foldr_filter_map]
    dsimp only [GameState.delete]
    rw [dedupComp_filter]
    congr 1
    refine List.filter_congr fun x _ => ?_
    simp [bne]
  simp only [e2eGsMk, pair_eval, hTransEq, hChallEq, hCompEq]
  rfl

theorem cost_e2eDeleteE_le {Γ : List (Ty S)} (q : ℕ) (s : Expr O' Γ (e2eGsTy ℓ))
    (pos : Expr O' Γ posTy) :
    (e2eDeleteE q s pos).cost ≤ s.cost + pos.cost + 190 * q + 150 := by
  have hm34 : max (1 + 1 + 1) (1 + 1 + 1 + 1) = 4 := rfl
  have hm31 : max (1 + 1 + 1) 1 = 3 := rfl
  simp only [e2eDeleteE, e2eGsMk, e2eRecPos, e2eGsSt, e2eGsB, e2eGsWin, e2eGsEpoch, e2eGsIdx,
    e2eGsTL, e2eGsTrans, e2eGsChall, e2eGsComp, e2eGsMaxAcc, e2eGsLeaks, e2eGsCorrs, posEq,
    posSender, posEpoch, posIdx, boolEq, Expr.cost, Expr.v0, Expr.v1, Expr.v2, hm34, hm31]
  omega

def e2eAcceptE {Γ : List (Ty S)} (q : ℕ) (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool)
    (st' : Expr O' Γ GhostStT) (pos : Expr O' Γ posTy) : Expr O' Γ (e2eGsTy ℓ) :=
  .letE (.pair (e2eDeleteE q s pos) (.pair p (.pair st' pos)))
    (let s1 : Expr O' _ (e2eGsTy ℓ) := .fst .v0
     let p0 : Expr O' _ .bool := .fst (.snd .v0)
     let st0 : Expr O' _ GhostStT := .fst (.snd (.snd .v0))
     let pos0 : Expr O' _ posTy := .snd (.snd (.snd .v0))
     let pEpoch : Expr O' _ .nat := posEpoch pos0
     let pIdx : Expr O' _ .nat := posIdx pos0
     e2eGsMk
       (pSet (e2eGsSt s1) p0 st0)
       (e2eGsB s1) (e2eGsWin s1)
       (pSet (e2eGsEpoch s1) p0 (maxN (pGet (e2eGsEpoch s1) p0) pEpoch))
       (e2eGsIdx s1) (e2eGsTL s1) (e2eGsTrans s1) (e2eGsChall s1) (e2eGsComp s1)
       (maxAccSet (e2eGsMaxAcc s1) p0 pEpoch
         (maxN (maxAccGet (e2eGsMaxAcc s1) p0 pEpoch) pIdx))
       (e2eGsLeaks s1) (e2eGsCorrs s1))

@[simp] theorem eval_e2eAcceptE {Γ : List (Ty S)} (q : ℕ) (s : Expr O' Γ (e2eGsTy ℓ))
    (p : Expr O' Γ .bool) (st' : Expr O' Γ GhostStT) (pos : Expr O' Γ posTy) (ρ : Env Γ)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (P : Party) (p0 : Pos)
    (hbnd : SmListBounded q st)
    (hs : s.eval ρ = e2eGsEnc st) (hp : p.eval ρ = partyEnc P) (hpos : pos.eval ρ = posEnc p0) :
    (e2eAcceptE q s p st' pos).eval ρ = e2eGsEnc (st.accept P (st'.eval ρ) p0) := by
  unfold e2eAcceptE GameState.accept
  rw [letE_eval]
  have hdel := eval_e2eDeleteE q s pos ρ st p0 hbnd hs hpos
  have hp0 : (Expr.pair (e2eDeleteE q s pos) (.pair p (.pair st' pos))).eval ρ =
      (e2eGsEnc (st.delete p0), (partyEnc P, (st'.eval ρ, posEnc p0))) := by
    simp [Expr.eval, hdel, hp, hpos]
  rw [hp0]; clear hp0
  set s₁ := st.delete p0
  set ρ₁ := Env.cons (t := .prod (e2eGsTy ℓ) (.prod .bool (.prod GhostStT posTy)))
    (e2eGsEnc s₁, (partyEnc P, (st'.eval ρ, posEnc p0))) ρ
  have hstUpd :
      (pSet (e2eGsSt (.fst (Expr.v0 (O := O')))) (.fst (.snd (Expr.v0 (O := O'))))
        (.fst (.snd (.snd (Expr.v0 (O := O')))))).eval ρ₁ =
      (Function.update s₁.st P (st'.eval ρ) .A, Function.update s₁.st P (st'.eval ρ) .B) := by
    rw [pSet_eval _ _ _ ρ₁ s₁.st P rfl rfl]
    rfl
  have hepUpd :
      (pSet (e2eGsEpoch (.fst (Expr.v0 (O := O')))) (.fst (.snd (Expr.v0 (O := O'))))
        (maxN (pGet (e2eGsEpoch (.fst (Expr.v0 (O := O')))) (.fst (.snd (Expr.v0 (O := O')))))
          (posEpoch (.snd (.snd (.snd (Expr.v0 (O := O')))))))).eval ρ₁ =
      (Function.update s₁.epoch P (max (s₁.epoch P) p0.epoch) .A,
       Function.update s₁.epoch P (max (s₁.epoch P) p0.epoch) .B) := by
    rw [pSet_eval _ _ _ ρ₁ s₁.epoch P rfl rfl, maxN_eval, pGet_eval _ _ ρ₁ s₁.epoch P rfl rfl]
    rfl
  have hmaUpd :
      (maxAccSet (e2eGsMaxAcc (.fst (Expr.v0 (O := O')))) (.fst (.snd (Expr.v0 (O := O'))))
        (posEpoch (.snd (.snd (.snd (Expr.v0 (O := O'))))))
        (maxN (maxAccGet (e2eGsMaxAcc (.fst (Expr.v0 (O := O'))))
          (.fst (.snd (Expr.v0 (O := O'))))
          (posEpoch (.snd (.snd (.snd (Expr.v0 (O := O')))))))
          (posIdx (.snd (.snd (.snd (Expr.v0 (O := O')))))))).eval ρ₁ =
      ((fun t => if Party.A = P ∧ t = p0.epoch then max (s₁.maxAcc .A t) p0.idx else s₁.maxAcc .A t),
       (fun t => if Party.B = P ∧ t = p0.epoch then max (s₁.maxAcc .B t) p0.idx else s₁.maxAcc .B t)) := by
    cases P <;> {
      dsimp only [ρ₁, maxAccSet, maxAccGet, pSet, pGet, e2eGsMaxAcc, posEpoch, posIdx, maxN, leN,
        e2eGsEnc, posEnc, partyEnc, Expr.eval, Expr.v0, Env.get]
      refine Prod.ext (funext fun t => ?_) (funext fun t => ?_) <;> {
        by_cases ht : t = p0.epoch <;> simp [ht, Nat.max_def]
      }
    }
  simp only [e2eGsMk, pair_eval, hstUpd, hepUpd, hmaUpd]
  rfl

theorem cost_e2eAcceptE_le {Γ : List (Ty S)} (q : ℕ) (s : Expr O' Γ (e2eGsTy ℓ))
    (p : Expr O' Γ .bool) (st' : Expr O' Γ GhostStT) (pos : Expr O' Γ posTy) :
    (e2eAcceptE q s p st' pos).cost ≤
      s.cost + p.cost + st'.cost + 2 * pos.cost + 190 * q + 650 := by
  have hdel := cost_e2eDeleteE_le (ℓ := ℓ) (O' := O') q s pos
  simp only [e2eAcceptE, e2eGsMk, e2eGsSt, e2eGsB, e2eGsWin, e2eGsEpoch, e2eGsIdx, e2eGsTL,
    e2eGsTrans, e2eGsChall, e2eGsComp, e2eGsMaxAcc, e2eGsLeaks, e2eGsCorrs, pSet, pGet,
    maxAccSet, maxAccGet, maxN, leN, posEpoch, posIdx, Expr.cost, Expr.v0] at hdel ⊢
  omega

def e2eTrivialE {Γ : List (Ty S)} (q Δ : ℕ) (s : Expr O' Γ (e2eGsTy ℓ))
    (pos : Expr O' Γ posTy) : Expr O' Γ .bool :=
  .letE (.pair s pos)
    (let s0 : Expr O' _ (e2eGsTy ℓ) := .fst .v0
     let pos0 : Expr O' _ posTy := .snd .v0
     orE (e2eCompContainsE q s0 pos0)
       (.and (.not (.anyB q (e2eGsTrans s0) (posEq (e2eRecPos .v0) (.snd .v1))))
             (.not (healedByE (e2eGsTL s0) Δ (posEpoch pos0)))))

@[simp] theorem eval_e2eTrivialE {Γ : List (Ty S)} (q Δ : ℕ) (s : Expr O' Γ (e2eGsTy ℓ))
    (pos : Expr O' Γ posTy) (ρ : Env Γ)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (p0 : Pos)
    (hbnd : SmListBounded q st)
    (hs : s.eval ρ = e2eGsEnc st) (hp : pos.eval ρ = posEnc p0) :
    (e2eTrivialE q Δ s pos).eval ρ = st.trivial Δ p0 := by
  have htTrans : ((st.trans.map (e2eRecEncWith st.comp)).take q) =
      st.trans.map (e2eRecEncWith st.comp) :=
    List.take_of_length_le (by simpa using hbnd.trans_le)
  unfold e2eTrivialE GameState.trivial
  rw [letE_eval]
  have hp0 : (Expr.pair s pos).eval ρ = (e2eGsEnc st, posEnc p0) := by
    simp [Expr.eval, hs, hp]
  rw [hp0]; clear hp0
  set ρ₁ := Env.cons (t := .prod (e2eGsTy ℓ) posTy) (e2eGsEnc st, posEnc p0) ρ
  rw [orE_eval, and_eval, not_eval, not_eval]
  have hcomp := eval_e2eCompContainsE q (.fst (Expr.v0 (O := O'))) (.snd (Expr.v0 (O := O')))
    ρ₁ st p0 hbnd.dedupComp_le rfl rfl
  have hheal : (healedByE (e2eGsTL (.fst (Expr.v0 (O := O')))) Δ
      (posEpoch (.snd (Expr.v0 (O := O'))))).eval ρ₁ = healedBy st.tL Δ p0.epoch :=
    healedByE_eval _ Δ _ ρ₁
  have hany : (Expr.anyB q (e2eGsTrans (.fst (Expr.v0 (O := O'))))
      (posEq (e2eRecPos .v0) (.snd .v1))).eval ρ₁ =
      st.trans.any (fun r => r.pos == p0) := by
    dsimp only [Expr.eval]
    have hg : (e2eGsTrans (.fst (Expr.v0 (O := O')))).eval ρ₁ =
        st.trans.map (e2eRecEncWith st.comp) := rfl
    rw [hg, htTrans, any_map_eq]
    congr 1
    funext r
    simp [ρ₁, e2eRecPos, e2eRecEncWith, posEq_eval, Expr.eval, Expr.v0, Expr.v1]
  rw [hcomp, hany, hheal]

theorem cost_e2eTrivialE_le {Γ : List (Ty S)} (q Δ : ℕ) (s : Expr O' Γ (e2eGsTy ℓ))
    (pos : Expr O' Γ posTy) :
    (e2eTrivialE q Δ s pos).cost ≤ s.cost + pos.cost + bits Δ + 100 * q + 100 := by
  let t0 : Ty S := .prod (e2eGsTy ℓ) posTy
  have hm34 : max (1 + 1 + 1) (1 + 1 + 1 + 1) = 4 := rfl
  have hcomp := cost_e2eCompContainsE_le (ℓ := ℓ) (O' := O') q
    (.fst .v0 : Expr O' (t0 :: Γ) (e2eGsTy ℓ)) (.snd .v0)
  simp only [e2eTrivialE, e2eGsTrans, e2eGsTL, e2eRecPos, healedByE, leN, posEq, posSender,
    posEpoch, posIdx, boolEq, orE, Expr.cost, Expr.v0, Expr.v1, hm34] at hcomp ⊢
  omega

/-- Linear `O(q)` `SM.GameState.corrAllowed s P` over `e2eGsTy ℓ` using cached `e2eRecComp`. -/
def e2eCorrAllowedE {Γ : List (Ty S)} (q : ℕ) (s : Expr O' Γ (e2eGsTy ℓ))
    (p : Expr O' Γ .bool) : Expr O' Γ .bool :=
  .letE (.pair s p)
    (let s0 : Expr O' (.prod (e2eGsTy ℓ) .bool :: Γ) (e2eGsTy ℓ) := .fst .v0
     .and
       (.not (.anyB q (e2eGsChall s0) (boolEq (posSender .v0) (otherE (.snd .v1)))))
       (.not (.anyB q (e2eGsTrans s0)
         (.and (boolEq (posSender (e2eRecPos .v0)) (otherE (.snd .v1)))
               (.not (e2eRecComp .v0))))))

@[simp] theorem eval_e2eCorrAllowedE {Γ : List (Ty S)} (q : ℕ) (s : Expr O' Γ (e2eGsTy ℓ))
    (p : Expr O' Γ .bool) (ρ : Env Γ)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (P : Party)
    (hbnd : SmListBounded q st)
    (hs : s.eval ρ = e2eGsEnc st) (hp : p.eval ρ = partyEnc P) :
    (e2eCorrAllowedE q s p).eval ρ = st.corrAllowed P := by
  have htChall : ((st.chall.map posEnc).take q) = st.chall.map posEnc :=
    List.take_of_length_le (by simpa using hbnd.chall_le)
  have htTrans : ((st.trans.map (e2eRecEncWith st.comp)).take q) =
      st.trans.map (e2eRecEncWith st.comp) :=
    List.take_of_length_le (by simpa using hbnd.trans_le)
  unfold e2eCorrAllowedE GameState.corrAllowed
  rw [letE_eval]
  have hp0 : (Expr.pair s p).eval ρ = (e2eGsEnc st, partyEnc P) := by
    simp [Expr.eval, hs, hp]
  rw [hp0]; clear hp0
  set ρ₁ := Env.cons (t := .prod (e2eGsTy ℓ) .bool) (e2eGsEnc st, partyEnc P) ρ
  rw [and_eval, not_eval, not_eval]
  have hc1 : (Expr.anyB q (e2eGsChall (.fst (Expr.v0 (O := O'))))
      (boolEq (posSender .v0) (otherE (.snd .v1)))).eval ρ₁ =
      st.chall.any (fun pos => pos.sender == P.other) := by
    dsimp only [Expr.eval]
    have hg : (e2eGsChall (.fst (Expr.v0 (O := O')))).eval ρ₁ = st.chall.map posEnc := rfl
    rw [hg, htChall, any_map_eq]
    congr 1
    funext pos
    rcases pos with ⟨sender, _, _⟩
    cases sender <;> cases P <;> rfl
  have hc2 : (Expr.anyB q (e2eGsTrans (.fst (Expr.v0 (O := O'))))
      (.and (boolEq (posSender (e2eRecPos .v0)) (otherE (.snd .v1)))
            (.not (e2eRecComp .v0)))).eval ρ₁ =
      st.trans.any (fun r => r.pos.sender == P.other && !st.comp.contains r.pos) := by
    dsimp only [Expr.eval]
    have hg : (e2eGsTrans (.fst (Expr.v0 (O := O')))).eval ρ₁ =
        st.trans.map (e2eRecEncWith st.comp) := rfl
    rw [hg, htTrans, any_map_eq]
    congr 1
    funext r
    rcases r with ⟨⟨sender, _, _⟩, _, _⟩
    cases sender <;> cases P <;> rfl
  rw [hc1, hc2]

theorem cost_e2eCorrAllowedE_le {Γ : List (Ty S)} (q : ℕ) (s : Expr O' Γ (e2eGsTy ℓ))
    (p : Expr O' Γ .bool) :
    (e2eCorrAllowedE q s p).cost ≤ s.cost + p.cost + 75 * q + 35 := by
  have hm34 : max (1 + 1 + 1) (1 + 1 + 1 + 1) = 4 := rfl
  simp only [e2eCorrAllowedE, e2eGsChall, e2eGsTrans, e2eRecPos, e2eRecComp, posSender,
    otherE, boolEq, Expr.cost, Expr.v0, Expr.v1, hm34]
  omega

/-- `O(1)` `SM.GameState.afterCorr s P` over `e2eGsTy ℓ` when `s.corrAllowed P = true`. -/
def e2eAfterCorrAllowedE {Γ : List (Ty S)} (s : Expr O' Γ (e2eGsTy ℓ))
    (p : Expr O' Γ .bool) : Expr O' Γ (e2eGsTy ℓ) :=
  .letE (.pair s p)
    (let s0 : Expr O' (.prod (e2eGsTy ℓ) .bool :: Γ) (e2eGsTy ℓ) := .fst .v0
     .letE (e2eLeakE s0 (maxN (.fst (e2eGsEpoch s0)) (.snd (e2eGsEpoch s0))))
       (let s2 : Expr O' _ (e2eGsTy ℓ) := .v0
        let s0' : Expr O' _ (e2eGsTy ℓ) := .fst .v1
        let p0' : Expr O' _ .bool := .snd .v1
        e2eGsMk (e2eGsSt s2) (e2eGsB s2) (e2eGsWin s2) (e2eGsEpoch s2) (e2eGsIdx s2)
          (e2eGsTL s2) (e2eGsTrans s2) (e2eGsChall s2) (e2eGsComp s2) (e2eGsMaxAcc s2)
          (e2eGsLeaks s2)
          (.cons (.pair p0' (pGet (e2eGsEpoch s0') p0')) (e2eGsCorrs s2))))

@[simp] theorem eval_e2eAfterCorrAllowedE {Γ : List (Ty S)} (s : Expr O' Γ (e2eGsTy ℓ))
    (p : Expr O' Γ .bool) (ρ : Env Γ)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (P : Party)
    (hallow : st.corrAllowed P = true)
    (hs : s.eval ρ = e2eGsEnc st) (hp : p.eval ρ = partyEnc P) :
    (e2eAfterCorrAllowedE s p).eval ρ = e2eGsEnc (st.afterCorr P) := by
  unfold e2eAfterCorrAllowedE
  rw [letE_eval]
  have hp0 : (Expr.pair s p).eval ρ = (e2eGsEnc st, partyEnc P) := by
    simp [Expr.eval, hs, hp]
  rw [hp0]; clear hp0
  set ρ₁ := Env.cons (t := .prod (e2eGsTy ℓ) .bool) (e2eGsEnc st, partyEnc P) ρ
  rw [letE_eval]
  have hleak := eval_e2eLeakE (.fst (Expr.v0 (O := O')))
    (maxN (.fst (e2eGsEpoch (.fst .v0))) (.snd (e2eGsEpoch (.fst .v0)))) ρ₁ st rfl
  have hmax : (maxN (.fst (e2eGsEpoch (.fst (Expr.v0 (O := O')))))
      (.snd (e2eGsEpoch (.fst .v0)))).eval ρ₁ = max (st.epoch .A) (st.epoch .B) := by
    simp [ρ₁, maxN_eval, e2eGsEpoch, e2eGsEnc, Expr.eval, Expr.v0]
  rw [hmax] at hleak
  rw [hleak]
  have hdedup : dedupComp (st.afterCorr P).comp = dedupComp st.comp :=
    dedupComp_afterCorr_eq st P hallow
  have htrans_eq :
      (st.afterCorr P).trans.map (e2eRecEncWith (st.afterCorr P).comp) =
        st.trans.map (e2eRecEncWith st.comp) := by
    have htr : (st.afterCorr P).trans = st.trans := rfl
    rw [htr]
    refine List.map_congr_left fun r _ => ?_
    have hcont : (st.afterCorr P).comp.contains r.pos = st.comp.contains r.pos := by
      rw [← dedupComp_contains, hdedup, dedupComp_contains]
    dsimp only [e2eRecEncWith]
    rw [hcont]
  cases P <;> {
    dsimp only [ρ₁, e2eGsMk, e2eGsSt, e2eGsB, e2eGsWin, e2eGsEpoch, e2eGsIdx, e2eGsTL,
      e2eGsTrans, e2eGsChall, e2eGsComp, e2eGsMaxAcc, e2eGsLeaks, e2eGsCorrs, pGet, Expr.eval,
      Expr.v0, Expr.v1, e2eGsEnc, partyEnc]
    rw [hdedup, htrans_eq]
    rfl
  }

theorem cost_e2eAfterCorrAllowedE_le {Γ : List (Ty S)} (s : Expr O' Γ (e2eGsTy ℓ))
    (p : Expr O' Γ .bool) :
    (e2eAfterCorrAllowedE s p).cost ≤ s.cost + p.cost + 310 := by
  let t0 : Ty S := .prod (e2eGsTy ℓ) .bool
  have hleak := cost_e2eLeakE_le (ℓ := ℓ) (O' := O')
    (.fst .v0 : Expr O' (t0 :: Γ) (e2eGsTy ℓ))
    (maxN (.fst (e2eGsEpoch (.fst .v0))) (.snd (e2eGsEpoch (.fst .v0))))
  simp only [e2eAfterCorrAllowedE, maxN, leN, pGet, e2eGsMk, e2eGsSt, e2eGsB, e2eGsWin,
    e2eGsEpoch, e2eGsIdx, e2eGsTL, e2eGsTrans, e2eGsChall, e2eGsComp, e2eGsMaxAcc, e2eGsLeaks,
    e2eGsCorrs, Expr.cost, Expr.v0, Expr.v1] at hleak ⊢
  omega

def e2eInWindowE {Γ : List (Ty S)} (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool) :
    Expr O' Γ .bool :=
  .letE (.pair s p)
    (.not (sendsInE (.snd .v0) (pGet (e2eGsEpoch (.fst .v0)) (.snd .v0))))

@[simp] theorem eval_e2eInWindowE {Γ : List (Ty S)} (s : Expr O' Γ (e2eGsTy ℓ))
    (p : Expr O' Γ .bool) (ρ : Env Γ)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (P : Party)
    (hs : s.eval ρ = e2eGsEnc st) (hp : p.eval ρ = partyEnc P) :
    (e2eInWindowE s p).eval ρ = inWindow st P := by
  unfold e2eInWindowE inWindow
  rw [letE_eval]
  have hp0 : (Expr.pair s p).eval ρ = (e2eGsEnc st, partyEnc P) := by
    simp [Expr.eval, hs, hp]
  rw [hp0]; clear hp0
  set ρ₁ := Env.cons (t := .prod (e2eGsTy ℓ) .bool) (e2eGsEnc st, partyEnc P) ρ
  dsimp only [Expr.eval]
  rw [sendsInE_eval _ _ ρ₁ P rfl, pGet_eval _ _ ρ₁ st.epoch P rfl rfl]

theorem cost_e2eInWindowE_le {Γ : List (Ty S)} (s : Expr O' Γ (e2eGsTy ℓ))
    (p : Expr O' Γ .bool) :
    (e2eInWindowE s p).cost ≤ s.cost + p.cost + 40 := by
  have hb0 : bits 0 = 1 := by decide
  have hb1 : bits 1 = 1 := by decide
  have hb2 : bits 2 = 2 := by decide
  simp only [e2eInWindowE, sendsInE, pGet, e2eGsEpoch, Expr.cost, Expr.v0, hb0, hb1, hb2]
  omega

def e2eSendOKE {Γ : List (Ty S)} (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool) :
    Expr O' Γ .bool :=
  .letE (.pair s p)
    (.not (.and (.snd .v0) (.eqN (.snd (e2eGsEpoch (.fst .v0))) (.nat 0))))

@[simp] theorem eval_e2eSendOKE {Pt : Type} (decT : PublicKey → Option Pt)
    (encT : Pt → PublicKey) {Γ : List (Ty S)} (s : Expr O' Γ (e2eGsTy ℓ))
    (p : Expr O' Γ .bool) (ρ : Env Γ)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (P : Party)
    (hs : s.eval ρ = e2eGsEnc st) (hp : p.eval ρ = partyEnc P) :
    (e2eSendOKE s p).eval ρ = (configRefuseEarlyBobCorr decT encT).sendOK st P := by
  cases P <;> simp [e2eSendOKE, configRefuseEarlyBobCorr, configR1OnCurve,
    CryptoGames.SM.configR1, noBobSendInEpoch0, e2eGsEpoch, e2eGsEnc, partyEnc, nat_beq_eq_decide,
    hs, hp, Expr.eval, Expr.v0]

theorem cost_e2eSendOKE_le {Γ : List (Ty S)} (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool) :
    (e2eSendOKE s p).cost ≤ s.cost + p.cost + 20 := by
  have hb0 : bits 0 = 1 := by decide
  simp only [e2eSendOKE, e2eGsEpoch, Expr.cost, Expr.v0, hb0]
  omega

def e2eCorrOKE {Γ : List (Ty S)} (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool) :
    Expr O' Γ .bool :=
  .letE (.pair s p)
    (let s0 : Expr O' _ (e2eGsTy ℓ) := .fst .v0
     let p0 : Expr O' _ .bool := .snd .v0
     let epA : Expr O' _ .nat := .fst (e2eGsEpoch s0)
     let epB : Expr O' _ .nat := .snd (e2eGsEpoch s0)
     let okA10 : Expr O' _ .bool := .not (.and (.not p0) (.lt epA (.nat 10)))
     let okB0 : Expr O' _ .bool := .not (.and p0 (.eqN epB (.nat 0)))
     let okB10 : Expr O' _ .bool := .not (.and p0 (.lt epA (.nat 10)))
     .and (.and okA10 okB0) okB10)

@[simp] theorem eval_e2eCorrOKE {Pt : Type} (decT : PublicKey → Option Pt)
    (encT : Pt → PublicKey) {Γ : List (Ty S)} (s : Expr O' Γ (e2eGsTy ℓ))
    (p : Expr O' Γ .bool) (ρ : Env Γ)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (P : Party)
    (hs : s.eval ρ = e2eGsEnc st) (hp : p.eval ρ = partyEnc P) :
    (e2eCorrOKE s p).eval ρ = (configRefuseEarlyBobCorr decT encT).corrOK st P := by
  cases P <;> simp [e2eCorrOKE, configRefuseEarlyBobCorr, configR1OnCurve,
    CryptoGames.SM.configR1, noAliceCorrWhileAliceBelowEpoch10, noBobCorrInEpoch0,
    noBobCorrWhileAliceBelowEpoch10, e2eGsEpoch, e2eGsEnc, partyEnc, nat_beq_eq_decide, hs, hp,
    Expr.eval, Expr.v0]

theorem cost_e2eCorrOKE_le {Γ : List (Ty S)} (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool) :
    (e2eCorrOKE s p).cost ≤ s.cost + p.cost + 55 := by
  have hb0 : bits 0 = 1 := by decide
  have hb10 : bits 10 = 4 := by decide
  simp only [e2eCorrOKE, e2eGsEpoch, Expr.cost, Expr.v0, hb0, hb10]
  omega

end GsBookkeeping

section InTransit

variable {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

local notation "S" => e2eSig ℓ
local notation "OO" => e2eOps ℓ P C K decT encT

def e2eInTransitE {Γ : List (Ty S)} (q : ℕ) (s : Expr OO Γ (e2eGsTy ℓ))
    (qParty : Expr OO Γ .bool) (c : Expr OO Γ (B 32)) : Expr OO Γ (.opt (e2eRecTy ℓ)) :=
  .letE (.pair s (.pair qParty c))
    (.findB q (e2eGsTrans (.fst .v0))
      (.and (boolEq (posSender (e2eRecPos .v0)) (.fst (.snd .v1)))
            (bytesEqE (e2eRecCt .v0) (.snd (.snd .v1)))))

private theorem bytes_beq_eq_decide (x y : Bytes) : (x == y) = decide (x = y) := by
  cases h : (x == y) <;> simp_all [beq_iff_eq]

@[simp] theorem eval_e2eInTransitE {Γ : List (Ty S)} (q : ℕ) (s : Expr OO Γ (e2eGsTy ℓ))
    (qParty : Expr OO Γ .bool) (c : Expr OO Γ (B 32)) (ρ : Env Γ)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (Q : Party)
    (htrans : st.trans.length ≤ q)
    (hs : s.eval ρ = e2eGsEnc st) (hq : qParty.eval ρ = partyEnc Q) :
    (e2eInTransitE q s qParty c).eval ρ =
      (st.inTransit Q (c.eval ρ)).map (e2eRecEncWith st.comp) := by
  have htTrans : ((st.trans.map (e2eRecEncWith st.comp)).take q) =
      st.trans.map (e2eRecEncWith st.comp) :=
    List.take_of_length_le (by simpa using htrans)
  unfold e2eInTransitE GameState.inTransit
  rw [letE_eval]
  have hp0 : (Expr.pair s (.pair qParty c)).eval ρ =
      (e2eGsEnc st, (partyEnc Q, c.eval ρ)) := by
    simp [Expr.eval, hs, hq]
  rw [hp0]; clear hp0
  set ρ₁ := Env.cons (t := .prod (e2eGsTy ℓ) (.prod .bool (B 32)))
    (e2eGsEnc st, (partyEnc Q, c.eval ρ)) ρ
  dsimp only [Expr.eval]
  have hg : (e2eGsTrans (.fst (Expr.v0 (O := OO)))).eval ρ₁ =
      st.trans.map (e2eRecEncWith st.comp) := rfl
  rw [hg, htTrans, find?_map_eq]
  congr 2
  funext r
  rcases r with ⟨⟨sender, _, _⟩, _, ct⟩
  cases sender <;> cases Q
  · change (true && (ct == (c.eval ρ : Bytes))) = (true && decide (ct = c.eval ρ))
    simp [bytes_beq_eq_decide]
  · rfl
  · rfl
  · change (true && (ct == (c.eval ρ : Bytes))) = (true && decide (ct = c.eval ρ))
    simp [bytes_beq_eq_decide]

theorem cost_e2eInTransitE_le {Γ : List (Ty S)} (q : ℕ) (s : Expr OO Γ (e2eGsTy ℓ))
    (qParty : Expr OO Γ .bool) (c : Expr OO Γ (B 32)) :
    (e2eInTransitE q s qParty c).cost ≤ s.cost + qParty.cost + c.cost + 130 * q + 25 := by
  have hm34 : max (1 + 1 + 1) (1 + 1 + 1 + 1) = 4 := rfl
  simp only [e2eInTransitE, e2eGsTrans, e2eRecPos, e2eRecCt, posSender, boolEq, cost_bytesEqE,
    Expr.cost, Expr.v0, Expr.v1, hm34]
  omega

end InTransit

end Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping

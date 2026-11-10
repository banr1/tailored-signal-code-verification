/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Session.ACD19.SM.CostedTables
public import LibsignalBinary.Specifications.CryptoGames.SM.Construction

/-!
# CKA and ACD19 Fig. 8 reduction tables

**Checked by Lean.** Shared `ReductionDsl` signature, operation tables, samplers, target CKA
interface, and source game codecs (`CKA.spec`, `SM.spec`, `SM.specDF`) for Continuous Key Agreement
and the ACD19 Fig. 8 secure-messaging reductions.
-/

@[expose] public section

namespace CryptoGames.CKA

open ReductionDsl OracleSpec OracleComp

/-- Base value sorts of a CKA scheme and the ACD19 Fig. 8 SM construction built over it. -/
inductive CKASort
  | kc | γ | ccoins | t | i | kr | sig | k | ss | rs | msg | ct
  deriving DecidableEq

@[reducible] def CKASort.den (KC Γ CCoins T I KR RSt K SS RS M E : Type) : CKASort → Type
  | .kc => KC
  | .γ => Γ
  | .ccoins => CCoins
  | .t => T
  | .i => I
  | .kr => KR
  | .sig => RSt
  | .k => K
  | .ss => SS
  | .rs => RS
  | .msg => M
  | .ct => E

/-- Signature for CKA and ACD19 Fig. 8 reductions, assigning unit size to every `CKASort`. -/
@[reducible] def ckaSig (KC Γ CCoins T I KR RSt K SS RS M E : Type) : Sig where
  Base := CKASort
  den := CKASort.den KC Γ CCoins T I KR RSt K SS RS M E
  sz := fun _ _ => 1

@[reducible] def ckaHdrTy (KC Γ CCoins T I KR RSt K SS RS M E : Type) :
    Ty (ckaSig KC Γ CCoins T I KR RSt K SS RS M E) :=
  .prod .nat (.opt (.base .t))

@[reducible] def ckaHdrCtTy (KC Γ CCoins T I KR RSt K SS RS M E : Type) :
    Ty (ckaSig KC Γ CCoins T I KR RSt K SS RS M E) :=
  .prod (ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E) (.base .ct)

/-- Primitive CKA, PRF-PRNG, and FS-AEAD operations for ACD19 Fig. 8 reductions, including the
fallback ciphertext constant `defaultE` (DEV-SM15). -/
inductive CKAOp
  | ckaInitA
  | ckaInitB
  | ckaSend
  | ckaReceive
  | prngInit
  | prngUp
  | fsInitSender
  | fsInitReceiver
  | fsSend
  | fsReceive (B : ℕ)
  | eqT
  | eqI
  | eqM
  | eqE
  | lamI
  | defaultE
  deriving DecidableEq

/-- Operation table for `CKAOp` at unit cost, except `fsReceive B` which clamps the message index to
`B` at cost `bits B`. -/
@[reducible] def ckaOps {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    (ckaInitA : KC → Γ)
    (ckaInitB : KC → Γ)
    (ckaSend : Γ → CCoins → Γ × T × I)
    (ckaReceive : Γ → T → Γ × I)
    (prngInit : KR → RSt)
    (prngUp : RSt → I → RSt × K)
    (fsInitSender : K → SS)
    (fsInitReceiver : K → RS)
    (fsSend : SS → SM.Construction.Header T → M → SS × E)
    (fsReceive : RS → SM.Construction.Header T → E → Option (RS × ℕ × M))
    (eqT : T → T → Bool)
    (eqI : I → I → Bool)
    (eqM : M → M → Bool)
    (eqE : E → E → Bool)
    (lam : I)
    (defaultE : E) :
    Ops (ckaSig KC Γ CCoins T I KR RSt K SS RS M E) where
  Op := CKAOp
  dom := fun
    | .ckaInitA => .base .kc
    | .ckaInitB => .base .kc
    | .ckaSend => .prod (.base .γ) (.base .ccoins)
    | .ckaReceive => .prod (.base .γ) (.base .t)
    | .prngInit => .base .kr
    | .prngUp => .prod (.base .sig) (.base .i)
    | .fsInitSender => .base .k
    | .fsInitReceiver => .base .k
    | .fsSend =>
      .prod (.base .ss) (.prod (ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E) (.base .msg))
    | .fsReceive _ =>
      .prod (.base .rs) (ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)
    | .eqT => .prod (.base .t) (.base .t)
    | .eqI => .prod (.base .i) (.base .i)
    | .eqM => .prod (.base .msg) (.base .msg)
    | .eqE => .prod (.base .ct) (.base .ct)
    | .lamI => .unit
    | .defaultE => .unit
  cod := fun
    | .ckaInitA => .base .γ
    | .ckaInitB => .base .γ
    | .ckaSend => .prod (.base .γ) (.prod (.base .t) (.base .i))
    | .ckaReceive => .prod (.base .γ) (.base .i)
    | .prngInit => .base .sig
    | .prngUp => .prod (.base .sig) (.base .k)
    | .fsInitSender => .base .ss
    | .fsInitReceiver => .base .rs
    | .fsSend => .prod (.base .ss) (.base .ct)
    | .fsReceive _ => .opt (.prod (.base .rs) (.prod .nat (.base .msg)))
    | .eqT => .bool
    | .eqI => .bool
    | .eqM => .bool
    | .eqE => .bool
    | .lamI => .base .i
    | .defaultE => .base .ct
  eval := fun
    | .ckaInitA, kc => ckaInitA kc
    | .ckaInitB, kc => ckaInitB kc
    | .ckaSend, (γ, r) => ckaSend γ r
    | .ckaReceive, (γ, t) => ckaReceive γ t
    | .prngInit, kr => prngInit kr
    | .prngUp, (σ, i) => prngUp σ i
    | .fsInitSender, k => fsInitSender k
    | .fsInitReceiver, k => fsInitReceiver k
    | .fsSend, (ss, h, m) => fsSend ss h m
    | .fsReceive B, (rs, h, e) =>
      (fsReceive rs h e).map fun (rs', i, m) => (rs', min i B, m)
    | .eqT, (t₁, t₂) => eqT t₁ t₂
    | .eqI, (i₁, i₂) => eqI i₁ i₂
    | .eqM, (m₁, m₂) => eqM m₁ m₂
    | .eqE, (e₁, e₂) => eqE e₁ e₂
    | .lamI, () => lam
    | .defaultE, () => defaultE
  cost := fun
    | .fsReceive B => bits B
    | _ => 1

/-- Instantiate `ckaOps` from concrete `CKAScheme`, `PRFPRNG`, and `FSAEADScheme` structures. -/
@[reducible] def ckaSchemeOps {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (SM.Construction.Header T) M E)
    (lam : I) :
    Ops (ckaSig KC Γ CCoins T I KR RSt K SS RS M E) :=
  ckaOps cka.initA cka.initB cka.send cka.receive prng.init prng.up
    fs.initSender fs.initReceiver fs.send fs.receive
    (· == ·) (· == ·) (· == ·) (· == ·) lam default

inductive CKASamp
  | bit | kr | kc | ccoins | i | k
  deriving DecidableEq

/-- Coin and key samplers for CKA and Fig. 8 reductions at unit cost per sample. -/
@[reducible] def ckaSamplers {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    (sampKR : ProbComp KR)
    (sampKC : ProbComp KC)
    (sampCCoins : ProbComp CCoins)
    (sampI : ProbComp I)
    (sampK : ProbComp K) :
    Samplers (ckaSig KC Γ CCoins T I KR RSt K SS RS M E) where
  Samp := CKASamp
  sDom := fun _ => .unit
  sTy := fun
    | .bit => .bool
    | .kr => .base .kr
    | .kc => .base .kc
    | .ccoins => .base .ccoins
    | .i => .base .i
    | .k => .base .k
  samp := fun
    | .bit, _ => ($ᵗ Bool : ProbComp Bool)
    | .kr, _ => sampKR
    | .kc, _ => sampKC
    | .ccoins, _ => sampCCoins
    | .i, _ => sampI
    | .k, _ => sampK
  sCost := fun _ => 1

inductive CKATag
  | send | sendBad | chall | receive | corr
  deriving DecidableEq

/-- Target oracle interface for `unifSpec + CKA.spec Γ CCoins T I` with unit query cost and
`ckaSamplers`. -/
@[reducible] def ckaIface (KC Γ CCoins T I KR RSt K SS RS M E : Type)
    (sampKR : ProbComp KR)
    (sampKC : ProbComp KC)
    (sampCCoins : ProbComp CCoins)
    (sampI : ProbComp I)
    (sampK : ProbComp K) :
    Iface (ckaSig KC Γ CCoins T I KR RSt K SS RS M E)
      (unifSpec + CKA.spec Γ CCoins T I) where
  fwdU n := query (spec := unifSpec + CKA.spec Γ CCoins T I) (.inl n)
  uCost := 1
  Tag := CKATag
  dom := fun
    | .send => .bool
    | .sendBad => .prod .bool (.base .ccoins)
    | .chall => .bool
    | .receive => .bool
    | .corr => .bool
  cod := fun
    | .send => .opt (.prod (.base .t) (.base .i))
    | .sendBad => .opt (.prod (.base .t) (.base .i))
    | .chall => .opt (.prod (.base .t) (.base .i))
    | .receive => .opt .unit
    | .corr => .opt (.base .γ)
  enc := fun
    | .send, p => .inr (.inl (.inl (.inl (.inl (SM.partyDec p)))))
    | .sendBad, (p, r) => .inr (.inl (.inl (.inl (.inr (SM.partyDec p, r)))))
    | .chall, p => .inr (.inl (.inl (.inr (SM.partyDec p))))
    | .receive, p => .inr (.inl (.inr (SM.partyDec p)))
    | .corr, p => .inr (.inr (SM.partyDec p))
  dec := fun
    | .send, _, r => r
    | .sendBad, _, r => r
    | .chall, _, r => r
    | .receive, _, r => r
    | .corr, _, r => r
  qCost := fun _ => 1
  smp := ckaSamplers sampKR sampKC sampCCoins sampI sampK

@[reducible] def ckaQ (KC Γ CCoins T I KR RSt K SS RS M E : Type) :
    Ty (ckaSig KC Γ CCoins T I KR RSt K SS RS M E) :=
  .sum
    (.sum
      (.sum
        (.sum .bool (.prod .bool (.base .ccoins)))
        .bool)
      .bool)
    .bool

@[reducible] def ckaR (KC Γ CCoins T I KR RSt K SS RS M E : Type) :
    Ty (ckaSig KC Γ CCoins T I KR RSt K SS RS M E) :=
  .sum
    (.sum
      (.sum
        (.sum
          (.opt (.prod (.base .t) (.base .i)))
          (.opt (.prod (.base .t) (.base .i))))
        (.opt (.prod (.base .t) (.base .i))))
      (.opt .unit))
    (.opt (.base .γ))

/-- Source game codec for `CKA.spec` (`codecCost = 6`). -/
@[reducible] def ckaCodec (KC Γ CCoins T I KR RSt K SS RS M E : Type) :
    GameCodec (ckaSig KC Γ CCoins T I KR RSt K SS RS M E)
      (CKA.spec Γ CCoins T I) where
  Q := ckaQ KC Γ CCoins T I KR RSt K SS RS M E
  R := ckaR KC Γ CCoins T I KR RSt K SS RS M E
  qenc := fun
    | .inl (.inl (.inl (.inl P))) => .inl (.inl (.inl (.inl (SM.partyEnc P))))
    | .inl (.inl (.inl (.inr (P, r)))) => .inl (.inl (.inl (.inr (SM.partyEnc P, r))))
    | .inl (.inl (.inr P)) => .inl (.inl (.inr (SM.partyEnc P)))
    | .inl (.inr P) => .inl (.inr (SM.partyEnc P))
    | .inr P => .inr (SM.partyEnc P)
  rdec := fun
    | .inl (.inl (.inl (.inl _))), .inl (.inl (.inl (.inl r))) => r
    | .inl (.inl (.inl (.inl _))), _ => none
    | .inl (.inl (.inl (.inr _))), .inl (.inl (.inl (.inr r))) => r
    | .inl (.inl (.inl (.inr _))), _ => none
    | .inl (.inl (.inr _)), .inl (.inl (.inr r)) => r
    | .inl (.inl (.inr _)), _ => none
    | .inl (.inr _), .inl (.inr r) => r
    | .inl (.inr _), _ => none
    | .inr _, .inr r => r
    | .inr _, _ => none
  codecCost := 6

/-! ## Fig. 8 SM source game codecs -/

@[reducible] def ckaRrTy (KC Γ CCoins T I KR RSt K SS RS M E : Type) :
    Ty (ckaSig KC Γ CCoins T I KR RSt K SS RS M E) :=
  .sum .unit (.prod .nat (.prod .nat (.opt (.base .msg))))

/-- Tuple representation `(id, root, vS, vR, γ, curCkaMsg, tcur)` of `SM.Construction.PartyState`
in `ckaSig`. -/
@[reducible] def ckaPsTy (KC Γ CCoins T I KR RSt K SS RS M E : Type) :
    Ty (ckaSig KC Γ CCoins T I KR RSt K SS RS M E) :=
  .prod .bool
    (.prod (.base .sig)
      (.prod (.opt (.base .ss))
        (.prod (.tbl (.opt (.base .rs)))
          (.prod (.base .γ)
            (.prod (.opt (.base .t)) .nat)))))

def ckaPsDec {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    (v : (ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E).denote) :
    SM.Construction.PartyState Γ T RSt SS RS :=
  ⟨SM.partyDec v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2.1, v.2.2.2.2.2.2⟩

@[reducible] def ckaSMQ (KC Γ CCoins T I KR RSt K SS RS M E : Type) :
    Ty (ckaSig KC Γ CCoins T I KR RSt K SS RS M E) :=
  .sum
    (.sum
      (.sum
        (.sum
          (.prod .bool (.prod (.base .msg) (.opt (.base .ccoins))))
          (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins))))))
        (.prod .bool (ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)))
      (.prod .bool (ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)))
    .bool

@[reducible] def ckaSMR (KC Γ CCoins T I KR RSt K SS RS M E : Type) :
    Ty (ckaSig KC Γ CCoins T I KR RSt K SS RS M E) :=
  .sum
    (.sum
      (.sum
        (.sum
          (.opt (ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E))
          (.opt (ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)))
        (.opt (ckaRrTy KC Γ CCoins T I KR RSt K SS RS M E)))
      (.opt (ckaRrTy KC Γ CCoins T I KR RSt K SS RS M E)))
    (.opt (ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E))

/-- Source game codec for the Fig. 8 `SM.spec` (`codecCost = 12`). -/
@[reducible] def ckaSMCodec (KC Γ CCoins T I KR RSt K SS RS M E : Type) :
    GameCodec (ckaSig KC Γ CCoins T I KR RSt K SS RS M E)
      (SM.spec (SM.Construction.PartyState Γ T RSt SS RS) M CCoins
        (SM.Construction.Header T × E)) where
  Q := ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E
  R := ckaSMR KC Γ CCoins T I KR RSt K SS RS M E
  qenc := fun
    | .inl (.inl (.inl (.inl (P, m, r)))) =>
      .inl (.inl (.inl (.inl (SM.partyEnc P, m, r))))
    | .inl (.inl (.inl (.inr (P, m₀, m₁, r)))) =>
      .inl (.inl (.inl (.inr (SM.partyEnc P, m₀, m₁, r))))
    | .inl (.inl (.inr (Q, c))) =>
      .inl (.inl (.inr (SM.partyEnc Q, c)))
    | .inl (.inr (Q, c)) =>
      .inl (.inr (SM.partyEnc Q, c))
    | .inr P =>
      .inr (SM.partyEnc P)
  rdec := fun
    | .inl (.inl (.inl (.inl _))), .inl (.inl (.inl (.inl r))) => r
    | .inl (.inl (.inl (.inl _))), _ => none
    | .inl (.inl (.inl (.inr _))), .inl (.inl (.inl (.inr r))) => r
    | .inl (.inl (.inl (.inr _))), _ => none
    | .inl (.inl (.inr _)), .inl (.inl (.inr r)) => r.map SM.smRrDec
    | .inl (.inl (.inr _)), _ => none
    | .inl (.inr _), .inl (.inr r) => r.map SM.smRrDec
    | .inl (.inr _), _ => none
    | .inr _, .inr r => r.map ckaPsDec
    | .inr _, _ => none
  codecCost := 12

@[reducible] def ckaSMQDF (KC Γ CCoins T I KR RSt K SS RS M E : Type) :
    Ty (ckaSig KC Γ CCoins T I KR RSt K SS RS M E) :=
  .sum (ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E)
    (.prod .bool
      (.prod (ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)
        (ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)))

@[reducible] def ckaSMRDF (KC Γ CCoins T I KR RSt K SS RS M E : Type) :
    Ty (ckaSig KC Γ CCoins T I KR RSt K SS RS M E) :=
  .sum (ckaSMR KC Γ CCoins T I KR RSt K SS RS M E)
    (.opt (ckaRrTy KC Γ CCoins T I KR RSt K SS RS M E))

/-- Source game codec for the Fig. 8 `SM.specDF` extending `ckaSMCodec` with `deliverForge`
(`codecCost = 13`). -/
@[reducible] def ckaSMCodecDF (KC Γ CCoins T I KR RSt K SS RS M E : Type) :
    GameCodec (ckaSig KC Γ CCoins T I KR RSt K SS RS M E)
      (SM.specDF (SM.Construction.PartyState Γ T RSt SS RS) M CCoins
        (SM.Construction.Header T × E)) where
  Q := ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E
  R := ckaSMRDF KC Γ CCoins T I KR RSt K SS RS M E
  qenc := fun
    | .inl q => .inl ((ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E).qenc q)
    | .inr (Q, c, c') => .inr (SM.partyEnc Q, c, c')
  rdec := fun
    | .inl q, .inl r => (ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E).rdec q r
    | .inl (.inl (.inl (.inl (.inl _)))), .inr _ => none
    | .inl (.inl (.inl (.inl (.inr _)))), .inr _ => none
    | .inl (.inl (.inl (.inr _))), .inr _ => none
    | .inl (.inl (.inr _)), .inr _ => none
    | .inl (.inr _), .inr _ => none
    | .inr _, .inr r => r.map SM.smRrDec
    | .inr _, .inl _ => none
  codecCost := 13

end CryptoGames.CKA

set_option autoImplicit false

namespace CryptoGames.CKA

open ReductionDsl OracleSpec OracleComp

def ckaPsEnc {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    (p : SM.Construction.PartyState Γ T RSt SS RS) :
    (ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E).denote :=
  (SM.partyEnc p.id, p.root, p.vS, p.vR, p.γ, p.curCkaMsg, p.tcur)

@[simp] theorem ckaPsDec_ckaPsEnc {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    (p : SM.Construction.PartyState Γ T RSt SS RS) :
    ckaPsDec (KC := KC) (CCoins := CCoins) (I := I) (KR := KR) (K := K) (M := M) (E := E)
      (ckaPsEnc p) = p := by
  cases p; simp [ckaPsEnc, ckaPsDec]

end CryptoGames.CKA

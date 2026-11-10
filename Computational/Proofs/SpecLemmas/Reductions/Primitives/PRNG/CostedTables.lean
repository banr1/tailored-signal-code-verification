/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Reductions.Primitives.CKA.CostedTables

/-!
# PRF-PRNG and Fig. 8 FS-AEAD reduction tables

**Checked by Lean.** Shared `ReductionDsl` signature, operation tables, samplers, target interfaces
(`PRFPRNG.spec` and `FSAEAD.spec` with `Header T` associated data), and source SM codecs for the
ACD19 Fig. 8 PRF-PRNG and FS-AEAD reductions.
-/

@[expose] public section

namespace CryptoGames.PRFPRNG

open ReductionDsl OracleSpec OracleComp

/-- Signature for ACD19 Fig. 8 PRF-PRNG and FS-AEAD reductions, aliased to `CKA.ckaSig`. -/
abbrev prngSig (KC Γ CCoins T I KR RSt K SS RS M E : Type) : Sig :=
  CKA.ckaSig KC Γ CCoins T I KR RSt K SS RS M E

abbrev prngSchemeOps {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (SM.Construction.Header T) M E)
    (lam : I) :
    Ops (prngSig KC Γ CCoins T I KR RSt K SS RS M E) :=
  CKA.ckaSchemeOps cka prng fs lam

abbrev prngSamplers {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    (sampKR : ProbComp KR)
    (sampKC : ProbComp KC)
    (sampCCoins : ProbComp CCoins)
    (sampI : ProbComp I)
    (sampK : ProbComp K) :
    Samplers (prngSig KC Γ CCoins T I KR RSt K SS RS M E) :=
  CKA.ckaSamplers sampKR sampKC sampCCoins sampI sampK

inductive PRNGTag
  | process | challPrng | challPrf | corr
  deriving DecidableEq

/-- Target oracle interface for `unifSpec + PRFPRNG.spec RSt I K` with unit query cost and
`prngSamplers`. -/
@[reducible] def prngIface (KC Γ CCoins T I KR RSt K SS RS M E : Type)
    (sampKR : ProbComp KR)
    (sampKC : ProbComp KC)
    (sampCCoins : ProbComp CCoins)
    (sampI : ProbComp I)
    (sampK : ProbComp K) :
    Iface (prngSig KC Γ CCoins T I KR RSt K SS RS M E)
      (unifSpec + PRFPRNG.spec RSt I K) where
  fwdU n := query (spec := unifSpec + PRFPRNG.spec RSt I K) (.inl n)
  uCost := 1
  Tag := PRNGTag
  dom := fun
    | .process => .opt (.base .i)
    | .challPrng => .opt (.base .i)
    | .challPrf => .base .i
    | .corr => .unit
  cod := fun
    | .process => .opt (.base .k)
    | .challPrng => .opt (.base .k)
    | .challPrf => .opt (.prod (.base .sig) (.base .k))
    | .corr => .opt (.base .sig)
  enc := fun
    | .process, i => .inr (.inl (.inl (.inl i)))
    | .challPrng, i => .inr (.inl (.inl (.inr i)))
    | .challPrf, i => .inr (.inl (.inr i))
    | .corr, () => .inr (.inr ())
  dec := fun
    | .process, _, r => r
    | .challPrng, _, r => r
    | .challPrf, _, r => r
    | .corr, _, r => r
  qCost := fun _ => 1
  smp := prngSamplers sampKR sampKC sampCCoins sampI sampK

abbrev prngSMCodec (KC Γ CCoins T I KR RSt K SS RS M E : Type) :
    GameCodec (prngSig KC Γ CCoins T I KR RSt K SS RS M E)
      (SM.spec (SM.Construction.PartyState Γ T RSt SS RS) M CCoins
        (SM.Construction.Header T × E)) :=
  CKA.ckaSMCodec KC Γ CCoins T I KR RSt K SS RS M E

abbrev prngSMCodecDF (KC Γ CCoins T I KR RSt K SS RS M E : Type) :
    GameCodec (prngSig KC Γ CCoins T I KR RSt K SS RS M E)
      (SM.specDF (SM.Construction.PartyState Γ T RSt SS RS) M CCoins
        (SM.Construction.Header T × E)) :=
  CKA.ckaSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E

@[reducible] def fsHdrRrTy (KC Γ CCoins T I KR RSt K SS RS M E : Type) :
    Ty (prngSig KC Γ CCoins T I KR RSt K SS RS M E) :=
  .sum .unit (.prod .nat (.opt (.base .msg)))

def fsHdrRrEnc {M : Type} : FSAEAD.ReceiveResult M → Unit ⊕ (ℕ × Option M)
  | .rejected => .inl ()
  | .accepted i m => .inr (i, m)

inductive FSHdrTag
  | tr | ch | cs | cr | dl | ij
  deriving DecidableEq

/-- Target oracle interface for `unifSpec + FSAEAD.spec SS RS (SM.Construction.Header T) M E` over
`prngSig`. -/
@[reducible] def fsaeadHeaderAdIface (KC Γ CCoins T I KR RSt K SS RS M E : Type)
    (sampKR : ProbComp KR)
    (sampKC : ProbComp KC)
    (sampCCoins : ProbComp CCoins)
    (sampI : ProbComp I)
    (sampK : ProbComp K) :
    Iface (prngSig KC Γ CCoins T I KR RSt K SS RS M E)
      (unifSpec + FSAEAD.spec SS RS (SM.Construction.Header T) M E) where
  fwdU n := query (spec := unifSpec + FSAEAD.spec SS RS (SM.Construction.Header T) M E) (.inl n)
  uCost := 1
  Tag := FSHdrTag
  dom := fun
    | .tr => .prod (CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E) (.base .msg)
    | .ch =>
      .prod (CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E)
        (.prod (.base .msg) (.base .msg))
    | .cs | .cr => .unit
    | .dl | .ij => CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  cod := fun
    | .tr | .ch => .opt (.base .ct)
    | .cs => .opt (.base .ss)
    | .cr => .opt (.prod (.base .ss) (.base .rs))
    | .dl | .ij => .opt (fsHdrRrTy KC Γ CCoins T I KR RSt K SS RS M E)
  enc := fun
    | .tr, x => .inr (.inl (.inl (.inl (.inl (.inl x)))))
    | .ch, x => .inr (.inl (.inl (.inl (.inl (.inr x)))))
    | .cs, x => .inr (.inl (.inl (.inl (.inr x))))
    | .cr, x => .inr (.inl (.inl (.inr x)))
    | .dl, x => .inr (.inl (.inr x))
    | .ij, x => .inr (.inr x)
  dec := fun
    | .tr, _, u => u
    | .ch, _, u => u
    | .cs, _, u => u
    | .cr, _, u => u
    | .dl, _, u => Option.map fsHdrRrEnc u
    | .ij, _, u => Option.map fsHdrRrEnc u
  qCost := fun _ => 1
  smp := prngSamplers sampKR sampKC sampCCoins sampI sampK

end CryptoGames.PRFPRNG

set_option autoImplicit false

namespace CryptoGames.PRFPRNG

open ReductionDsl OracleSpec OracleComp

abbrev prngOps {KC Γ CCoins T I KR RSt K SS RS M E : Type}
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
    Ops (prngSig KC Γ CCoins T I KR RSt K SS RS M E) :=
  CKA.ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

end CryptoGames.PRFPRNG

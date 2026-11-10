/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.SM.Game
public import LibsignalBinary.Specifications.CryptoGames.CKA.Defs
public import LibsignalBinary.Specifications.CryptoGames.PRNG.Defs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Defs

/-!
# The Signal-based SM scheme (ACD19 Fig. 8)

**Trusted in part.** The theorems of `Computational/Theorems/` use only the types `Header` and
`PartyState` from this file: read them. `initParty`, `send`, `receive`, `scheme` and the theorems
here are checked by Lean. See `Computational/docs/TRUSTED_BASE.md`.

Generic secure-messaging scheme of ACD19 §5.1 (Alwen, Coretti, Dodis, ePrint 2018/1037) built from a
continuous key agreement scheme `cka`, a root PRF-PRNG `prng`, and a per-epoch FS-AEAD scheme `fs`
(`Ratchet/LibsignalSMInstance.lean` instantiates it for libsignal).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.SM.Construction

/-- Message header `h = (t, T_t)` (`T = none` encodes `λ` in epoch `0`), passed as FS-AEAD
associated data.

**DEV-SM11 (formalization): no `FS-Stop`, `FS-Max` or `ℓ_prv`.** ACD19 Fig. 8 sends `ℓ_prv` so the
receiver can erase old sessions via `FS-Max` and `FS-Stop`. Here old sessions are retained, the
header is `(t, T)`, and old-epoch forgeries are handled in the SM game (DEV-SM7; see DEV-LS13 for
libsignal's `previous_counter`). -/
abbrev Header (T : Type) := ℕ × Option T

/-- Per-party state for ACD19 Fig. 8. -/
structure PartyState (Γ T Sig SS RS : Type) where
  /-- Party identifier (`A` or `B`). -/
  id : Party
  /-- Root PRF-PRNG state `σ_root`. -/
  root : Sig
  /-- Current sending FS-AEAD session `v[t_cur]`.

  **DEV-SM12 (formalization): only the current sending session is kept.** ACD19 Fig. 8 indexes
  `v[t]` for every `t`, whereas sending sessions of past epochs are never reused. -/
  vS : Option SS
  /-- Receiving FS-AEAD sessions `v[t]` indexed by epoch `t`. -/
  vR : ℕ → Option RS
  /-- CKA state `γ`. -/
  γ : Γ
  /-- Current CKA message `T_cur`. -/
  curCkaMsg : Option T
  /-- Current epoch counter `t_cur`. -/
  tcur : ℕ

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}

section Algorithms

variable (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)

/-- ACD19 Fig. 8 `Init-P(k)` for `k = (k_root, k_CKA)`: `B` initializes a sending session in epoch
`0` and `A` initializes the matching receiving session.

**DEV-SM13 (formalization): `λ` is explicit.** ACD19 Fig. 8 absorbs a fixed `λ` into the root RNG at
initialization (`P-Up(σ_root, λ)`) and uses `T = λ` as the initial CKA message; here `lam` is an
explicit parameter, the initial CKA message is `none`, and `receive` rejects new-epoch headers
carrying `none`. -/
def initParty (P : Party) (k : KR × KC) : PartyState Γ T Sig SS RS :=
  let out := prng.up (prng.init k.1) lam
  { id := P,
    root := out.1,
    vS := match P with
      | .A => none
      | .B => some (fs.initSender out.2),
    vR := match P with
      | .A => fun t => if t = 0 then some (fs.initReceiver out.2) else none
      | .B => fun _ => none,
    γ := match P with
      | .A => cka.initA k.2
      | .B => cka.initB k.2,
    curCkaMsg := none,
    tcur := 0 }

/-- ACD19 Fig. 8 `Send-P(m)` with CKA coins `r`: advances to a new sending epoch when due (`CKA-S`,
`P-Up`, `FS-Init-S`) and encrypts `m` under header `(t_cur, T_cur)`.

**DEV-SM14 (formalization): the SM coins are the CKA sender coins.** Coins `r` are passed directly
to `CKA-S` and consumed only when starting a new sending epoch.

**DEV-SM15 (formalization): an unreachable branch.** If `vS = none`, `send` returns `default`;
reachable states in a sending epoch always hold an active sending session. -/
def send [Inhabited E] (s : PartyState Γ T Sig SS RS) (m : M) (r : CCoins) :
    PartyState Γ T Sig SS RS × (Header T × E) :=
  let s₁ : PartyState Γ T Sig SS RS :=
    if s.id.sendsIn (s.tcur + 1) then
      let c := cka.send s.γ r
      let p := prng.up s.root c.2.2
      { s with tcur := s.tcur + 1, γ := c.1, curCkaMsg := some c.2.1, root := p.1,
               vS := some (fs.initSender p.2) }
    else s
  let h : Header T := (s₁.tcur, s₁.curCkaMsg)
  match s₁.vS with
  | some v =>
    let out := fs.send v h m
    ({ s₁ with vS := some out.1 }, (h, out.2))
  | none => (s₁, (h, default))

/-- ACD19 Fig. 8 `Rcv-P(c)` for `c = ((t, T), e)`: checks that `t` is a receiving epoch of `P` with
`t ≤ t_cur + 1`, initializes epoch `t_cur + 1` via `CKA-R`, `P-Up`, and `FS-Init-R` when needed, and
decrypts under `v[t]` (returning `none` on failure without mutating state). -/
def receive (s : PartyState Γ T Sig SS RS) (c : Header T × E) :
    Option (PartyState Γ T Sig SS RS × ℕ × ℕ × M) :=
  let t := c.1.1
  if s.id.sendsIn t || s.tcur + 1 < t then none else
  let s₁? : Option (PartyState Γ T Sig SS RS) :=
    if t = s.tcur + 1 then
      match c.1.2 with
      | none => none
      | some Tn =>
        let k := cka.receive s.γ Tn
        let p := prng.up s.root k.2
        some { s with tcur := t, γ := k.1, root := p.1,
                      vR := Function.update s.vR t (some (fs.initReceiver p.2)) }
    else some s
  match s₁? with
  | none => none
  | some s₁ =>
    match s₁.vR t with
    | none => none
    | some v =>
      match fs.receive v c.1 c.2 with
      | none => none
      | some (v', i, m) => some ({ s₁ with vR := Function.update s₁.vR t (some v') }, t, i, m)

/-- The ACD19 Fig. 8 SM scheme (DEV-SM11 to DEV-SM16), keyed by `(k_root, k_CKA)` with skip window
`fs.maxSkip`. -/
def scheme [Inhabited E] :
    SMScheme (KR × KC) (PartyState Γ T Sig SS RS) M CCoins (Header T × E) where
  initA := initParty cka prng fs lam .A
  initB := initParty cka prng fs lam .B
  send := send cka prng fs
  receive := receive cka prng fs
  maxSkip := fs.maxSkip

end Algorithms

end CryptoGames.SM.Construction

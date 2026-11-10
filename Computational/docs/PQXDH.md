# PQXDH: what is modelled, and the bound at deployment parameters

The PQXDH key agreement of `libsignal-protocol` at tag `v0.105.4` (commit
`b2a5c30f3245c1bcad04b27b1e752a38321c793d`). The model (`Computational/Specifications/{Pqxdh,Assumptions,SignalPqxdh}/`) mirrors these
libsignal paths:

| Role | libsignal function (modelled) |
|---|---|
| Initiator (Alice) | `process_prekey_bundle` → `pqxdh_initiate`, `initialize_alice_session` |
| Recipient (Bob) | `process_prekey` → `pqxdh_accept`, `initialize_bob_session` |
| Recipient, first message | `message_decrypt_prekey` |

The model-level headline `SignalPqxdh.Security.headlineδ` (statement `PqxdhCorrectAndSecureδ`, in
`Computational/Theorems/Lemmas.lean`) proves functional correctness and one-key random-oracle
key indistinguishability (`PqxdhKeyIndSecureδ`, under `GapSigEufCma`, `KemShCr`, and `GapDhWithSign`),
and one-key first-message authentication and payload privacy (`PqxdhAuth1KeySecureδ` in
`Computational/Specifications/Pqxdh/Security/Auth/Headline.lean`, game `Auth1KeyAdvantage` in
`Computational/Specifications/Pqxdh/Security/Auth/Game.lean`, under `GapSigEufCma`, `KemShCr`, `GapDhWithSign`, `PrfChainKey`, `PrfMsgKeys`, `AeadIndCpa`, and `PrfHmac`;
[DEV-C5](DEVIATIONS.md#dev-c5)); standalone statements and proofs of two-key `KeyInd` and `Auth`/`FirstMsg`
(`Pqxdh2KeyKeyIndSecureδ`, `PqxdhAuthSecureδ`, `Pqxdh2KeySecureδ`, `Pqxdh2KeyCorrectAndSecureδ` in
`Computational/Proofs/SignalPqxdh/TwoKeyAndAuthStatements.lean`) live in `Computational/Proofs/` outside
the trusted base. The statements about the compiled code are about the `libsignal-cli` AArch64 ELF in
PQXDH mode: Lemma 4 `libsignal_cli_pq_binary_correct_placed` and the Main Theorem
`libsignal_cli_pq_secure_elf_binary_placed`, both in placed form, in
`Computational/Theorems/Main.lean`; see [README.md](README.md) and
`TRUSTED_BASE.md`. The deviations from libsignal and from the papers are the
`DEV-PQ*` entries of [DEVIATIONS.md](DEVIATIONS.md).

## 1. libsignal source facts

Re-checked on 2026-10-07 at the commit above:

* `secrets = 0xFF^32 ‖ DH(IK_A,SPK_B) ‖ DH(EK_A,IK_B) ‖ DH(EK_A,SPK_B) ‖ [DH(EK_A,OPK_B)] ‖ ss`,
  `(ss, ct) = Kyber1024.Encaps(PQSPK_B)` (`pqxdh.rs:194-237`); Bob mirrors with
  `their_ephemeral_key.is_canonical()` first and `Decaps(PQSPK_B.sk, ct)` (`pqxdh.rs:326-376`).
* `HandshakeKeys::derive`: `HKDF-SHA256(salt = None, ikm = secrets)
  .expand("WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024", 96)` split 32/32/32 into
  `(root_key, chain_key @ index 0, pqr_key)` (`pqxdh.rs:70-92`).
* Bundle checks in `process_prekey_bundle` (`session.rs:207-230`), in this order: identity
  trusted (store hook); `XEdDSA.verify(IK_B, SPK_B.serialize(), σ_SPK)`;
  `XEdDSA.verify(IK_B, PQSPK_B.serialize(), σ_PQSPK)`. Same key, no domain-separation tag; the two
  messages are distinguished only by length and leading type byte (`0x05` vs `0x08`).
* `their_ratchet_key = SPK_B` (passed twice, `session.rs:249-250`).
* The first message's 8-byte MAC covers `IK_sender ‖ IK_receiver ‖ inner SignalMessage`; the KEM
  ciphertext and PQSPK are **not** authenticated by it. v0.105.4 is therefore in the regime of
  BJKS24 §5.3 (KEM binding property needed), not revision 3 (PQSPK/ct in AD).
* Last-resort PQSPK replay protection is delegated by libsignal to
  `KyberPreKeyStore::mark_kyber_pre_key_used` (a store hook here).

## 2. The bound at `deploymentSetup` (asymptotic / qualitative regime)

Closed-form security bounds from `Computational/Specifications/Pqxdh/Bound.lean` (Terms 1–5 show
the static capacity form `pqxdhKeyIndBound S`; Lemma 1 `PqxdhKeyIndSecureδ` on the one-key
random-oracle game under `GapSigEufCma`, `KemShCr`, and `GapDhWithSign` uses the tighter
activity-bounded `pqxdhKeyIndBoundActive S b.q_on ≤ pqxdhKeyIndBound S` (`pqxdhKeyIndBoundActive_le`,
with equality once $b.\mathrm{q\_on} \ge S.N_{\text{dh}}$), together with `kemDecapsFailureTerm` (defined in
`Bound.lean`, added by `pqxdhKeyIndAdvantageBoundActiveδ` in
`Computational/Specifications/Pqxdh/Security/HeadlineDelta.lean`)) and
`Computational/Specifications/Pqxdh/Security/Auth/Game.lean` (Terms 5b–10, `pqxdhAuthBound`, used by
Lemma 1's one-key `PqxdhAuth1KeySecureδ` and by the standalone two-key `PqxdhAuthSecureδ` proof),
evaluated symbolically in the assumption advantages at `deploymentSetup`: $S.N_{\text{id}} = 2^{20}$
principals, $S.N_{\text{recv}} = 2^5$ ($S.N_{\text{spk\_tot}} = 2^{25}$ signed/Kyber prekey bundles),
$S.N_{\text{opk}} = S.N_{\text{no\_opk}} = 2^5$ ($S.N_{\text{recv\_tot}} = 2^{31}$ receiver sessions),
$S.N_{\text{send\_opk}} = S.N_{\text{send\_no\_opk}} = 2^9$ ($S.N_{\text{send\_opk\_tot}} = 2^{29}$,
$S.N_{\text{send\_tot}} = 2^{30}$ initiator sessions, $S.N_{\text{sess\_tot}} = 3 \cdot 2^{30}$ total
sessions, $S.N_{\text{dh}} = 2^{20} + 2^{25} + 2^{30} + 2^{30} = 2{,}182{,}086{,}656 \approx 2^{31.0231}$
clamped X25519 keys):

| Term | Expression (`Bound.lean` / `HeadlineDelta.lean`) | Evaluated at `deploymentSetup` | Note |
|---|---|---|---|
| **1. XEdDSA bundle signatures** | `S.N_id * epsSig` | $2^{20} \cdot \varepsilon_{\text{Sig}}$ | Hop $G_{0.1} \to G_1$ (`GapSigEufCma` across $N_{\text{id}}$ principals in one-key `KeyInd`; `SigEufCma` in standalone two-key) |
| **2. X25519 key collision** | `(S.N_dh * (S.N_dh - 1) + S.N_send_tot * (S.N_send_tot - 1)) / 2 ^ 251` | $(2{,}182{,}086{,}656 \cdot 2{,}182{,}086{,}655 + 2^{30} (2^{30} - 1)) / 2^{251} \approx 2^{-188.641} \approx 1.634 \times 10^{-57}$ | Hop $G_{0.1} \to G_1$ (unconditional clamped-scalar collision bound `2^-250`¹ over unordered pairs) |
| **3. Kyber-1024 `KemShCr`** | `S.N_spk_tot * S.N_send_tot * epsKemShCr` | $2^{55} \cdot \varepsilon_{\text{KemShCr}}$ | Hop $G_2 \to G_3$ (`KemShCr` shared-secret binding) |
| **4. Kyber-1024 `pk` collision** | `(S.N_spk_tot * (S.N_spk_tot - 1)) / 2 ^ 256` | $2^{25} (2^{25} - 1) / 2^{256} \approx 2^{-206} \approx 9.723 \times 10^{-63}$ | Hop $G_2 \to G_3$ (unconditional `kem_coll_bound = 2^-255` per unordered pair: `pk` depends only on the 32-byte `d`) |
| **5. Single-pair Gap-DH** | `2 * (S.N_spk_tot * (S.N_id + S.N_send_tot) + S.N_id * S.N_send_tot + S.N_opk_tot * S.N_send_opk_tot) * epsGapDh` | $(2^{60} + 2^{56} + 2^{51} + 2^{46}) \cdot \varepsilon_{\text{GapDH}} = \frac{17{,}441}{16{,}384} \cdot 2^{60} \cdot \varepsilon_{\text{GapDH}} \approx 2^{60.09} \cdot \varepsilon_{\text{GapDH}}$ | Hop $G_3 \to G_{3.5}$ (`GapDhWithSign` in one-key `KeyInd`, `GapDH` in standalone two-key; `DH1`–`DH4` in `HkdfRO`, Cases A–D) |
| **Subtotal (`pqxdhKeyIndBound S`; `pqxdhKeyIndBoundActive S b.q_on ≤ pqxdhKeyIndBound S`, with equality once $b.\mathrm{q\_on} \ge S.N_{\text{dh}} \approx 2^{31.02}$)** | **Sum of Terms 1–5 (`pqxdhKeyIndBoundActive` replaces `S.N_*` in Terms 1–5, incl. collision Terms 2 & 4, with `min b.q_on S.N_*`)** | **$2^{20}\varepsilon_{\text{Sig}} + 2^{55}\varepsilon_{\text{KemShCr}} + \frac{17{,}441}{16{,}384} \cdot 2^{60}\varepsilon_{\text{GapDH}} + \approx 2^{-188.641}$ (static cap, attained at $b.\mathrm{q\_on} \ge S.N_{\text{dh}}$)** | **Lemma 1 one-key `KeyInd` (`pqxdhKeyIndImpl1KeyRo`; `pqxdhKeyIndAdvantageBoundActiveδ S b.q_on` adds `2 · N_send_tot · N_spk_tot · δ_kem = 2^56 · δ_kem`, which equals $2^{-118}$ at $\delta_{\text{kem}} = 2^{-174}$)** |
| **5b. Responder-to-send `ekA` collision** | `2 * S.N_send_tot * S.N_recv_tot / 2 ^ 250` | $2 \cdot 2^{30} \cdot 2^{31} / 2^{250} = 2^{-188} \approx 2.549 \times 10^{-57}$ | Hop $G_3 \to G_{3.5}$ (standalone two-key `Auth` Subcase `2b-i`: fresh initiator `x25519Base ekASk` collides mod cofactor-8 with a prior responder receive's `r.ekAPk`) |
| **6. Epoch-1 Root KDF (`RootKdfRO`)** | `rootKdfRoTerm S q_roRoot = 2 * S.N_sess_tot * (q_roRoot + S.N_sess_tot) / 2 ^ 256` | $6 \cdot 2^{30} \cdot (q_{\text{roRoot}} + 3 \cdot 2^{30}) / 2^{256}$ (e.g., $\approx 3 \cdot 2^{-185}$ at $q_{\text{roRoot}} = 2^{40}$, $\approx 3 \cdot 2^{-161}$ at $q_{\text{roRoot}} = 2^{64}$) | Hop $G_{3.5} \to G_{3.6}$ (standalone two-key `Auth`: `RootKey::create_chain` as RO; unconditional root-key guessing + RO-input collision) |
| **7. Epoch-1 Chain KDF (`PrfChainKey`)** | `2 * S.N_sess_tot * epsPrfCk` | $3 \cdot 2^{31} \cdot \varepsilon_{\text{PrfCk}} \approx 2^{32.585} \cdot \varepsilon_{\text{PrfCk}}$ | Hop $G_{3.6} \to G_{3.7}$ (`ChainKey::message_keys` / `next_chain_key`) |
| **8. Message-keys KDF (`PrfMsgKeys`)** | `2 * S.N_sess_tot * epsPrfMsgKeys` | $3 \cdot 2^{31} \cdot \varepsilon_{\text{PrfMsgKeys}} \approx 2^{32.585} \cdot \varepsilon_{\text{PrfMsgKeys}}$ | Hop $G_{3.7} \to G_{3.8}$ (`MessageKeys::derive_keys` 80B) |
| **9. First-message `AeadIndCpa`** | `2 * S.N_send_tot * epsAeadCpa` | $2^{31} \cdot \varepsilon_{\text{AeadCpa}}$ | Hop $G_{3.8} \to G_4$ (one-time IND-CPA on fresh sends) |
| **10. First-message ciphertext integrity (`PrfHmac`)** | `2 * (2 * S.N_sess_tot * epsPrfHmac + S.N_recv_tot / 2 ^ 64)` | $3 \cdot 2^{32} \cdot \varepsilon_{\text{PrfHmac}} + 2^{-32}$ ($2^{-32} \approx 2.328 \times 10^{-10}$) | Hop $G_{3.8} \to G_5$ (multi-key INT-CTXT `AeadMuIntCtxt` over all session keys, incl. KCI, charged to `PrfHmac` making at most $S.N_{\text{recv\_tot}} + 1$ queries; $2^{-32}$ from at most $S.N_{\text{recv\_tot}}$ forgery attempts against an 8-byte MAC tag) |
| **Total (`pqxdhAuthBound`)** | **Sum of Terms 1–10 (incl. 5b)** | **Sum of reduction terms above $+ \; 2^{-32} + \text{collision terms}$** | **One-key `Auth`/`FirstMsg` in Lemma 1 (`PqxdhAuth1KeySecureδ`, plus `kemDecapsFailureTerm`; [DEV-C5](DEVIATIONS.md#dev-c5)); also the standalone two-key `PqxdhAuthSecureδ`; report cryptographic bit security separately from Term 10's protocol-inherent $2 \cdot S.N_{\text{recv\_tot}} / 2^{64} = 2^{-32}$ 8-byte MAC authenticity bound** |

¹ **Footnote on Term 2 (`(S.N_dh * (S.N_dh - 1) + S.N_send_tot * (S.N_send_tot - 1)) / 2 ^ 251`)**: Term 2 bounds the probability of a subgroup public-key collision across the $\binom{S.N_{\text{dh}}}{2}$ unordered pairs of honestly clamped X25519 keys (lower triangle) or an initiator `dh2` collision across the $\binom{S.N_{\text{send\_tot}}}{2}$ unordered pairs of initiator ephemeral slots (upper triangle), multiplying each unordered pair by `ec_coll_bound` $= 2^{-250}$ ($2^{-251}$ per pair would be false for real X25519; the $2^{251}$ denominator comes from the $\binom{N}{2} = N(N-1)/2$ unordered-pair factor). In standalone `Auth` (where initiator `dh2` is not separately tracked), the `N_dh(N_dh - 1) / 2^251` contribution already suffices and is bounded above by Term 2. Similarly, Term 4 sums `kem_coll_bound` $= 2^{-255}$ over the $\binom{S.N_{\text{spk\_tot}}}{2}$ unordered bundle pairs to give `S.N_spk_tot * (S.N_spk_tot - 1) / 2 ^ 256`. In Lemma 1's active bound `pqxdhKeyIndBoundActive S b.q_on`, Terms 2 and 4 take the active forms `(n_dh * (n_dh - 1) + n_send * (n_send - 1)) / 2 ^ 251` and `(n_spk * (n_spk - 1)) / 2 ^ 256` with $n_{\mathrm{dh}} = \min(b.\mathrm{q\_on}, S.N_{\text{dh}})$, $n_{\mathrm{send}} = \min(b.\mathrm{q\_on}, S.N_{\text{send\_tot}})$, and $n_{\mathrm{spk}} = \min(b.\mathrm{q\_on}, S.N_{\text{spk\_tot}})$. `kem_coll_bound` is a modelling hypothesis on the universally quantified `kemKeyGen`, not a fact stated by FIPS 203 (libsignal uses round-3 Kyber, [DEV-PQ2](DEVIATIONS.md#dev-pq2)). In Kyber the public key depends only on the 32-byte seed `d`, through $G = $ SHA3-512, so $\Pr[\mathit{pk} = t]$ is the number of `d` mapping to $t$ divided by $2^{256}$. If $G$ is modelled as a random function, two distinct `d` give the same public key with probability $1 - e^{-1/2} \approx 0.39$, and then a $2^{-256}$ bound would fail, while a three-way collision has probability $\approx 2^{-258.6}$, so $2^{-255}$ holds almost surely. The hypothesis can make the results say nothing about real Kyber, but cannot make them unsound. (Pointed out in Sam Schlesinger's review; the bound was weakened from $2^{-256}$ to $2^{-255}$ for this reason in #1143.)

**Why the computational terms at `deploymentSetup` and high query budgets ($b.\mathrm{q\_total} = 2^{40}$) are asymptotic/qualitative, whereas realistic query budgets ($b.\mathrm{q\_on}, b.\mathrm{q\_total} \ll 2^{30}$) give concrete bit-security numbers.**
Under Lemma 1 (`Computational/Specifications/Pqxdh/Security/Headline.lean`, `HeadlineDelta.lean`, `Bound.lean`, and `CostedBudgets.lean`),
the one-key `KeyInd` bound `pqxdhKeyIndBoundActive S b.q_on` replaces passive setup totals (across both the reduction coefficients and the X25519/Kyber collision terms) with active online-query caps $n_{\mathrm{id}} = \min(b.\mathrm{q\_on}, S.N_{\mathrm{id}})$, $n_{\mathrm{spk}} = \min(b.\mathrm{q\_on}, S.N_{\mathrm{spk\_tot}})$, $n_{\mathrm{opk}} = \min(b.\mathrm{q\_on}, S.N_{\mathrm{opk\_tot}})$, $n_{\mathrm{send}} = \min(b.\mathrm{q\_on}, S.N_{\mathrm{send\_tot}})$, $n_{\mathrm{send\_opk}} = \min(b.\mathrm{q\_on}, S.N_{\mathrm{send\_opk\_tot}})$, and $n_{\mathrm{dh}} = \min(b.\mathrm{q\_on}, S.N_{\mathrm{dh}})$ (bounded above by `pqxdhKeyIndBound S` via `pqxdhKeyIndBoundActive_le`, with equality once $b.\mathrm{q\_on} \ge S.N_{\mathrm{dh}}$). Each reduction $R_i(A)$ adds at most `stepCostBudget S b = 2 ^ 16 * (b.q_total + 1) ^ 2 + 2 ^ 15 * (b.q_total + 1) * (M_dh + M_sess) + 2 ^ 10 * (b.q_total + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) + 2 ^ 11 * M_dh ^ 2 + 2 ^ 8 * M_dh * M_sess` syntactic `ReductionDsl`
steps (where $M_{\mathrm{dh}} = \min(b.\mathrm{q\_total}, S.N_{\mathrm{dh}})$ and $M_{\mathrm{sess}} = \min(b.\mathrm{q\_total}, S.N_{\mathrm{sess\_tot}})$), making at
most $q_{\mathrm{sig}} \le 2 \cdot \min(S.N_{\mathrm{spk\_tot}}, S.N_{\mathrm{recv}}) = 64$ signing
queries ($2 \cdot S.N_{\mathrm{spk\_tot}} = 2^{26}$ in standalone two-key `Auth`),
$q_{\mathrm{ddh}} \le \mathrm{gdhQueryBudget}(S, b) = \min\bigl(4 \cdot b.\mathrm{q\_total}^2,\, 4 M_{\mathrm{ro}} M^{\mathrm{on}}_{\mathrm{sess}} + 2 M^{\mathrm{on}}_{\mathrm{sess}}(M^{\mathrm{on}}_{\mathrm{sess}} - 1)\bigr) + b.\mathrm{q\_total} + S.N_{\mathrm{dh}} + S.N_{\mathrm{sess\_tot}}$
decisional DH queries (where $M_{\mathrm{ro}} = \min(b.\mathrm{q\_ro}, b.\mathrm{q\_total})$, $M^{\mathrm{on}}_{\mathrm{sess}} = \min(\min(b.\mathrm{q\_on}, b.\mathrm{q\_total}), S.N_{\mathrm{sess\_tot}})$: session queries are online, so they are capped by $b.\mathrm{q\_on}$, unlike the $M_{\mathrm{sess}}$ of `stepCostBudget`), and
$q_{\mathrm{prim}} \le \mathrm{gdhPrimQueryBudget}(S, b) = 32(b.\mathrm{q\_total} - M^{\mathrm{on}}_{\mathrm{sess}}) + 16(M^{\mathrm{on}}_{\mathrm{sess}} + 1)(5 S.N_{\mathrm{dh}} + S.N_{\mathrm{sess\_tot}} + 12)$
primitive queries on $R_1, R_3$ (`primQueryBudget S b = 16 * (b.q_total + 1) * (5 * S.N_dh + S.N_sess_tot + 12)` on $R_2$). At `deploymentSetup` and $b.\mathrm{q\_on} = b.\mathrm{q\_ro} = b.\mathrm{q\_total} = 2^{40}$
($b.\mathrm{q\_roRoot} = 0$), $\mathrm{stepCostBudget} \approx 2^{96.00}$,
$q_{\mathrm{ddh}} \approx 2^{73.59}$, and $q_{\mathrm{prim}} \approx 2^{69.30}$ (and in the composed CLI
statements at $\ell = 1024$, `bhAdapterCostBudget`, `bhE2ECostBudget`, `ratchetCostBudget` / `fsRatchetCostBudget`, and `spkHopBudget` likewise clamp dynamic table sizes at $\min(b.\mathrm{q\_total}, S.N_*)$ and $n_{\mathrm{Inst}} = \min(q_{\mathrm{Start}}, n_{\mathrm{Send}})$). Although
$t' \approx 2^{96.00}$ sits roughly $30$ bits below the $\sim 2^{126}$-step threshold where generic
discrete logarithm on Curve25519 ($p \approx 2^{252}$) succeeds with probability $1$, Pollard's rho
gives the conjectured best-known-attack hardness estimate
$\varepsilon_{\text{GapDH}}(t_{\text{grp}}) \approx (t_{\text{grp}}^2 + q_{\mathrm{ddh}}) / 2^{252}$
(a heuristic generic-attack estimate, not a proven standard-model bound).
Because `GapDhWithSign` is a standard-model assumption over a concrete primitive record `P` (adversaries
can evaluate X25519 locally in $t'$ steps, not only via `primSpec`), setting $t_{\text{grp}} \propto t'$
at $b.\mathrm{q\_total} = 2^{40}$ ($t' \approx 2^{96.00}$) gives $(t')^2 / 2^{252} \approx 2^{-59.99}$ and makes Term 5
($c_3 \cdot \varepsilon_{\text{GapDH}} \approx 2^{60.09} \cdot 2^{-59.99} \approx 2^{+0.10} > 1$) vacuous at $q_{\mathrm{total}} = 2^{40}$
(whereas at $b.\mathrm{q\_total} \ll 2^{30}$, clamping $M_{\mathrm{dh}}, M_{\mathrm{sess}} \le b.\mathrm{q\_total}$ and active counts $\le b.\mathrm{q\_on}$ eliminates the passive $O(N_{\mathrm{dh}}^2)$ floor so $\mathrm{stepCostBudget}$ scales as $O(q_{\mathrm{total}}^2 + q_{\mathrm{total}} \log N_{\mathrm{dh}})$ even at `deploymentSetup`). Plugging runtime-independent 128-bit baselines
($\varepsilon_{\text{GapDH}} \le 2^{-127}$ or $2^{-120}$) into $b.\mathrm{q\_total} = 2^{40}$ at `deploymentSetup` is therefore invalid.

**Standard-model Curve25519 accounting, within Lemma 1's one-key ROM game (`KeyInd1KeyRoAdvantage` / `HkdfRO`, $t' \ll 2^{120}$).**
Here "standard-model" refers only to Curve25519 runtime accounting ($t_{\text{grp}} \le t'$, without
generic-group restrictions on X25519); Lemma 1 itself still bounds the one-key random-oracle game
`KeyInd1KeyRoAdvantage` (`HkdfRO`), not a ROM-free handshake game. With the active-count bound `pqxdhKeyIndBoundActive S b.q_on` and dynamic $M_* = \min(b.\mathrm{q\_total}, S.N_*)$ table clamping in `stepCostBudget`, `bhAdapterCostBudget`, and `bhE2ECostBudget`, both `deploymentSetup` at moderate query budgets ($b.\mathrm{q\_total} \le 2^{24}$) and enterprise/team setups give concrete non-vacuous Curve25519 Gap-DH margins against $t \le 2^{64}$ adversaries in Lemma 1 (`KeyInd1KeyRoAdvantage`) and Clause 2 of `CliPqxdhSecurityFor` (which additionally carries $+ 2 \cdot \varepsilon_{\mathrm{ro}}$ under
the `KeyIndRoGap` premise, [DEV-CLI16](DEVIATIONS.md#dev-cli16), where $\varepsilon_{\mathrm{ro}}$ is not
bounded in Lean; see [`READING_THE_THEOREMS.md`](READING_THE_THEOREMS.md) §3). The MAC-forgery supremum
`macForgeryProb` and the five companion session forgery and spurious-step suprema (`eps0IdealUnit`,
`epoch0ChainForgeryTerm`, `spuriousStepTerm`, `forgedEpochStartSpuriousStepTerm`, and
`spkSwapSpuriousStepTerm`) restrict `c < 2^32` and `ser.length < 2^32`, keeping all six non-vacuous
in the random-function / ROM heuristic ($\approx 2^{-64}$ per uniform-key tag test, heuristic, not
proved in Lean; [DEV-LS23](DEVIATIONS.md#dev-ls23), `TRUSTED_BASE.md` §4).
Active-session forgery in `SessionSecure`, `ModelSecure`, and `CliPqxdhSecurityFor` is therefore a
proved guarantee whose session multiplicities are listed in [DEV-LS31](DEVIATIONS.md#dev-ls31) and
[DEV-C14](DEVIATIONS.md#dev-c14) (scaling as $\sim 12 \cdot q_{\mathrm{ep}}^2 \cdot q^2 \cdot 2^{-64}$
per promoted session, non-vacuous for moderate per-session $q, q_{\mathrm{ep}}$), bounded below by
Libsignal's protocol-inherent 8-byte wire-MAC floor ($\approx 4 \cdot q_{\mathrm{DR}} \cdot 2^{-64}$,
e.g. $2^{-38}$ at $q_{\mathrm{DR}} = 2^{24}$ and $2^{-32}$ at $q_{\mathrm{DR}} = 2^{30}$). Because
the 64-bit wire-tag floor grows with forgery attempts regardless of reduction tightness, concrete
security summaries should report two separate numbers: (i) cryptographic (key-secrecy) bit security
from the computational reduction terms and 256-bit/Kyber statistical terms at runtime $t'$, and
(ii) the 8-byte wire-MAC authenticity bound as a separate function of receiver/delivery/epoch counts
($S.N_{\mathrm{recv\_tot}}$ in `pqxdhAuthBound`; $q_{\mathrm{Start}}$, per-session $q = qs(k)$, and
$q_{\mathrm{ep}}$ in [DEV-C14](DEVIATIONS.md#dev-c14)).

These expressions and evaluations are computed by hand from `Bound.lean` and `CostedBudgets.lean`; Lean does not check them.

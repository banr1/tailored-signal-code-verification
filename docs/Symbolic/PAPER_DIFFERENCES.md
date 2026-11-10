# Differences Between Our Lean Security Theorems and the Research Literature

This document explains how the machine-checked Lean 4 security theorems in `Symbolic/Theorems/` compare against the two primary formal-verification papers on Signal's post-quantum handshake and ratcheting protocols:

1. **Bhargavan, Jacomme, Kiefer, and Schmidt (USENIX Security 2024)** — *"Formal verification of the PQXDH Post-Quantum key agreement protocol for end-to-end secure messaging"* (hereafter **Bhargavan et al.**).
2. **Cheval, Jacomme, and Richards (IEEE S&P 2026)** — *"Automated formal analysis of Signal's Double Ratchet: attacks, fixes and security proofs"* (full version, April 2026; hereafter **Cheval et al.**).

This guide assumes no prior familiarity with either our Lean specifications or the two papers. Section 1 introduces the protocols and gives a bird's-eye comparison; Section 2 explains the threat models, role-naming conventions, and theorem inventory; Section 3 details all differences from Cheval et al. (2026); Section 4 details all differences from Bhargavan et al. (2024); Section 5 explains our ARM64 binary refinement theorems and their exact scope relative to the symbolic model; and Section 6 provides a theorem-by-theorem reference matrix.

---

## 1. Protocol Background and High-Level Comparison

### 1.1 How Modern Signal (`libsignal` v0.105.4) Establishes and Ratchets Keys

End-to-end encrypted messaging in Signal combines three cryptographic mechanisms into a single session lifecycle:

1. **PQXDH (Post-Quantum Extended Diffie-Hellman)** — Signal's asynchronous session-establishment handshake. Because a recipient (**Bob**) may be offline when a sender (**Alice**) wants to start a conversation, Bob pre-publishes a *prekey bundle* to Signal's untrusted server containing:
   - Bob's long-term X25519/XEdDSA identity public key (`IK_B`),
   - a medium-term X25519 signed prekey (`SPK_B`, signed under `IK_B`),
   - a medium-term or one-time post-quantum Kyber-1024 / ML-KEM-1024 signed prekey (`PQSPK_B`, signed under `IK_B`), and
   - an optional single-use X25519 one-time prekey (`OPK_B`, unsigned).

   Alice fetches Bob's bundle, verifies both signatures, generates a fresh ephemeral X25519 "base" key (`EK_A`), encapsulates a post-quantum shared secret (`ss`, ciphertext `ct`) to `PQSPK_B`, combines three or four X25519 Diffie-Hellman agreements (`DH1..DH4`) with `ss` inside HKDF-SHA256, and attaches `EK_A` and `ct` to her opening `PreKeySignalMessage`.

2. **The Double Ratchet (DR)** — Once a session is initialized, Alice and Bob continuously update their keys with every message:
   - **Symmetric-key chains (KDF chains)** advance a sending or receiving chain key (`CKs` / `CKr`) via HMAC-SHA256 for each consecutive message sent in one direction, deleting old chain keys to provide immediate per-message **Forward Secrecy (FS)** (a future state leak cannot decrypt past messages). Out-of-order messages are handled by temporarily caching bounded *skipped message-key seeds*.
   - **Asymmetric Diffie-Hellman ratchets (DH ratchets)** generate a fresh X25519 key pair (`DHs`) whenever the conversation changes direction, mixing a fresh DH shared secret into the session's root key (`RK`). This provides **Post-Compromise Security (PCS)**, also called *future secrecy* or *self-healing*: if an attacker steals a party's entire session state, security is automatically restored once the parties exchange uncompromised DH ratchet keys.

3. **SPQR and the Triple Ratchet** — In `libsignal` v0.105.4, the classical Double Ratchet is upgraded to the **Triple Ratchet** by running **SPQR (Sparse Post-Quantum Ratchet, V1)** alongside it. Initialized from a third 32-byte key output by PQXDH (`pqr`), SPQR runs an incremental ML-KEM-768 braid protocol across message headers (`pq_ratchet`) and produces post-quantum keys (`pqSalt`) that salt the HKDF derivation of each message's encryption and MAC keys.

### 1.2 Bird's-Eye Comparison

Neither research paper verifies the full composed protocol in its unrestricted threat model, and neither verifies implementation code:

- **Bhargavan et al. (2024)** verify **standalone PQXDH** (one handshake followed by a single `"hello"` confirmation message, with no ratcheting and no stored session state), using **ProVerif** for symbolic proofs under rich key compromises and **CryptoVerif** for computational post-quantum reductions under long-term identity-key compromise only.
- **Cheval et al. (2026)** verify **ProVerif** symbolic models of the Double Ratchet (`DR`), header-encryption variants (`DR-HE`, `DR-HE*`), an attacker-salted Triple Ratchet hook, and a composition with PQXDH (`DR-PQXDH*`). However, due to ProVerif state-space explosion (7 hours and 46 GB RAM), `DR-PQXDH*` had to be restricted to **a single PQXDH session, no one-time prekeys (`OPK`), no PQXDH key compromises, and no ratchet private-key (`DHs`) compromises**.
- **Our Lean 4 verification (`Symbolic/`)** works in **two layers**, both checked by Lean's kernel without `sorry`:
  1. **Symbolic Model Layer (`ModelSecurity.lean`)**: Models the complete `libsignal` v0.105.4 **`PQXDH ∘ SPQR (V1) ∘ Triple Ratchet`** composition in a single Dolev-Yao state machine (`DY.Libsignal.Composed.reachability`, using the DyLean framework) and proves **all ten symbolic security theorems** simultaneously **without** `DR-PQXDH*`'s scenario or compromise restrictions.
  2. **ARM64 Binary Refinement Layer (`Security.lean`, `Refinement.lean`, `RefinementPreservation.lean`, `Tests/ExternWitness.lean`)**: Proves that concrete ARM64 machine-code execution traces of the compiled `libsignal-cli` ELF binary (`cliElfBytes`, SHA-256 pinned, built from `libsignal` v0.105.4 and linked with stock `ld.lld`) refine the composed symbolic model and satisfy **all ten security queries directly on hardware traces**, subject to explicit CLI environment assumptions and concrete byte-collision bounds (`CollisionAfterExplainedPrefix`).

| Dimension | Bhargavan et al. (2024) | Cheval et al. (2026) | Our Symbolic Model (`Security/Model.lean`) | Our ARM64 Binary Theorems (`Theorems/Security.lean`, `Theorems/Refinement.lean`) |
|---|---|---|---|---|
| **Protocol verified** | Standalone PQXDH + 1 AEAD `"hello"` message (no ratchet) | Standalone `DR`, `DR-HE`/`DR-HE*`, attacker-salted `TR`, and restricted `DR-PQXDH*` | Full composed **`PQXDH ∘ SPQR (V1) ∘ Triple Ratchet`** (`libsignal` v0.105.4) | Full composed **`PQXDH ∘ SPQR (V1) ∘ Triple Ratchet`** in compiled ARM64 `libsignal-cli` ELF |
| **Mathematical model** | **Both** Symbolic (ProVerif) **and** Computational PQ reductions (CryptoVerif) | Symbolic (ProVerif + GSVerif lemmas) | Symbolic (DyLean in Lean 4 kernel) | Concrete ARM64 ISA byte traces refining Symbolic DyLean, up to byte collisions (`CollisionAfterExplainedPrefix`) |
| **Source / binary code verified?** | No (hand-written ProVerif / CryptoVerif models) | No (hand-written ProVerif models) | No (mechanized Lean spec matching `libsignal` structure) | **Yes** — compiled static ARM64 ELF (`cliElfBytes`), crypto externs axiomatized via `HooksMatchInterpretation` |
| **Participants & sessions** | Unbounded parties & sessions | Unbounded in `DR`; **1 PQXDH session only** in `DR-PQXDH*` | **Unbounded** honest/corrupt parties & **unbounded** sessions | **2 provisioned honest parties** (`alice ≠ bob`); multiple sequential sessions via `clearSession` |
| **PQXDH compromises & quantum breaks** | Full in ProVerif (`IK`, `SPK`, `PQSPK`, `OPK`, `BrokenDH`, `BrokenKEM`); `IK`-only in CryptoVerif | **Disabled** in `DR-PQXDH*` (no `OPK`, no PQXDH compromises, no `BrokenDH`/`BrokenKEM`) | **Full** (`IK`, `SPK`, `PQSPK`, `OPK`, corrupt PKI, `BrokenDH`, `BrokenKEM`) | **Full on 2-party setup** (`.leak` of `IK`, `SPK`, `PQSPK`, unused `OPK`, plus `.breakDH`/`.breakKEM`/`.invertDH`/`.invertKEM`; no corrupt PKI) |
| **Ratchet state compromises** | None (no ratchet state stored) | Full in `DR` (`RK`, `DHs`, `CKs`, `CKr`, `MK`); **no `DHs` compromise** in `DR-PQXDH*` and `DR-HE*` | **Full** (`RK`, `DHs`, `CKs`, `CKr`, `MK`, **plus** `ExposedSpqr`), including stale snapshots | **Full** on current `SessionRecord` (`RK`, `DHs`, `CKs`, `CKr`, skipped `seed`s, `pq_ratchet_state`) |
| **Curve25519 cofactor / encoding** | Prime-order DH in ProVerif; modulo subgroup in CryptoVerif | Prime-order ideal DH only (torsion attack out of model scope) | Non-canonical encodings (`Fin 4`), 8-torsion (`Fin 8`), low-order & `isCanonicalKey` checks | Byte-level X25519 u-coordinate, clamping, `is_torsion_free` (`X25519TorsionShiftsRejected`) |

---

## 2. Background Primer: Roles, Models, and Theorem Inventory

### 2.1 Warning on Role Naming: "Initiator" and "Responder" Are Swapped in Bhargavan et al.

A frequent source of confusion when comparing Signal papers is that **Bhargavan et al. (2024) invert `libsignal`'s and Cheval et al.'s role names**:

- In `libsignal`, Cheval et al. (2026), and **our Lean codebase**, **Alice** (the *initiator*) is the party who fetches a prekey bundle and sends the opening `PreKeySignalMessage`; **Bob** (the *responder*) is the party who uploaded the prekey bundle and accepts the `PreKeySignalMessage`.
- In **Bhargavan et al. (2024)**, prekey upload is treated as the first message of a synchronous two-message exchange. Consequently, Bhargavan et al. call the bundle uploader **Blake ($B$) the "Initiator"** and call the bundle fetcher **Alex ($A$) the "Responder"**. (Additionally, Figures 1 and 4 of Bhargavan et al. swap the subscripts $\mathsf{SK}_A$ and $\mathsf{SK}_B$ relative to their Appendix A; Appendix A uses $\mathsf{SK}_A$ for Alex and $\mathsf{SK}_B$ for Blake.)

| Protocol Action | `libsignal` & Our Lean Code | Cheval et al. (2026) | Bhargavan et al. (2024) |
|---|---|---|---|
| Fetches prekey bundle, encapsulates KEM, sends initial `PreKeySignalMessage` | **Alice** (`aliceStart`, logs `PQXDHEvent.AliceDone`) | **Initiator $I$** | **Responder Alex ($A$)** (logs `AlexOK`; **Theorem 7**) |
| Uploads prekey bundle, receives `PreKeySignalMessage`, decapsulates & confirms | **Bob** (`bobStart`, logs `PQXDHEvent.BobDone`) | **Responder $R$** | **Initiator Blake ($B$)** (logs `BlakeOK`; **Theorems 8 & 9**) |

To avoid confusion, our Lean identifiers (`alice_initiator_secrecy` / `AliceInitiatorSecrecy` for Theorem 7, and `bob_responder_secrecy` / `BobResponderSecrecy` for Theorem 9) name both the `libsignal` party and role explicitly: `alice_initiator_secrecy` proves Bhargavan et al.'s Theorem 7 ("Responder Secrecy" on Alex) for `libsignal` Alice (`AliceDone`), while `bob_responder_secrecy` proves Bhargavan et al.'s Theorem 9 ("Initiator Secrecy" on Blake) for `libsignal` Bob (`BobDone`).

### 2.2 Symbolic (Dolev-Yao) vs. Computational Security Proofs

Formal cryptography uses two complementary styles of proof:

1. **Symbolic (Dolev-Yao) verification** (used by ProVerif in both papers, and by DyLean in our Lean model):
   - Messages, keys, ciphertexts, and signatures are modeled as **algebraic terms** (trees of constructors) subject to explicit equational rules — for example, $\mathsf{dh}(\mathsf{dhPk}(a), b) = \mathsf{dh}(\mathsf{dhPk}(b), a)$ and $\mathsf{dec}(\mathsf{enc}(m, k, iv), k, iv) = m$.
   - Cryptography is idealized: an active network adversary controls the entire network (intercepting, dropping, modifying, reordering, and forging messages from any terms in its knowledge set `AttackerKnows`), can corrupt participants, and can trigger explicit state-leak transitions, **but** cannot guess fresh random numbers or invert hashes, ciphers, DH keys, or KEM ciphertexts unless an explicit compromise or cryptanalytic-break transition (`BrokenDH`, `BrokenKEM`) gives it that secret.
   - **Strength**: Scales to intricate state machines, unbounded ratcheting loops, fine-grained dynamic state compromises, and complex multi-session interactions that are intractable in manual game-hopping proofs.
   - **Limitation**: Does not by itself bound concrete bit-level advantage (e.g., $2^{-128}$) against polynomial-time or quantum algorithms, nor detect weaknesses inside underlying primitives (such as a biased RNG or a broken block cipher).

2. **Computational (game-hopping) verification** (used by CryptoVerif in Bhargavan et al., Theorems 2–6):
   - Keys and messages are bitstrings, the adversary is an arbitrary probabilistic (or quantum) algorithm, and security is reduced to concrete mathematical hardness assumptions (e.g., Gap Diffie-Hellman on Curve25519, IND-CCA + `SH-CR` of Kyber-1024, UF-CMA of XEdDSA, PRF/ROM assumptions on HKDF/SHA-256).

> **Fundamental Scope Difference:** Our `Symbolic/` Lean library contains **no CryptoVerif-style computational reductions** (Bhargavan et al.'s Theorems 2–6 have no computational counterpart in `Symbolic/`). Instead, we prove all symbolic Dolev-Yao properties of both papers in one unified composed model, and then **refine that symbolic model down to actual ARM64 machine code** (`Security.lean`, `Refinement.lean`), proving that every byte-level execution of the compiled binary either behaves as a valid symbolic trace satisfying all ten security theorems or hits an explicit concrete cryptographic collision (`CollisionAfterExplainedPrefix`).

### 2.3 Inventory of Our Top-Level Lean Theorems (`Symbolic/Theorems/`)

All proven statements live in `Symbolic/Theorems/` and `Symbolic/Specifications/`:

| Lean Theorem (`Symbolic/Theorems/`) | Underlying Specification | Paper Counterpart |
|---|---|---|
| `Proven.ForwardSecrecy.forward_secrecy` (`ModelSecurity.lean`) | `Composed.Security.ForwardSecrecy` (`Security/Model.lean`) | Cheval et al. (2026), Table 2 (`DR-PQXDH*` FS row) & §4.1.4 |
| `Proven.PostCompromiseSecurity.post_compromise_security` (`ModelSecurity.lean`) | `Composed.Security.PostCompromiseSecurity` (`Security/Model.lean`) | Cheval et al. (2026), Table 2 (`DR-PQXDH*` PCS row) & §4.1.4 |
| `Proven.Handshake.alice_initiator_secrecy` (`ModelSecurity.lean`) | `Composed.Security.AliceInitiatorSecrecy` (`Security/Model.lean`) | Bhargavan et al. (2024), **Theorem 7** (App. A) |
| `Proven.Handshake.authentication` (`ModelSecurity.lean`) | `Composed.Security.Authentication` (`Security/Model.lean`) | Bhargavan et al. (2024), **Theorem 8** (App. A) |
| `Proven.Handshake.bob_responder_secrecy` (`ModelSecurity.lean`) | `Composed.Security.BobResponderSecrecy` (`Security/Model.lean`) | Bhargavan et al. (2024), **Theorem 9** (App. A) |
| `Proven.Handshake.peer_authentication` (`ModelSecurity.lean`) | `Composed.Security.PeerAuthentication` (`Security/Model.lean`) | Bhargavan et al. (2024), **Theorem 1 (1)** (§4, App. A) |
| `Proven.Handshake.handshake_forward_secrecy` (`ModelSecurity.lean`) | `Composed.Security.HandshakeForwardSecrecy` (`Security/Model.lean`) | Bhargavan et al. (2024), **Theorem 1 (2)** (§4, App. A) |
| `Proven.Handshake.kci_resistance` (`ModelSecurity.lean`) | `Composed.Security.KCIResistance` (`Security/Model.lean`) | Bhargavan et al. (2024), **Theorem 1 (3)** (§4, App. A) |
| `Proven.Handshake.session_independence` (`ModelSecurity.lean`) | `Composed.Security.SessionIndependence` (`Security/Model.lean`) | Bhargavan et al. (2024), **Theorem 1 (4)** (§4, App. A) |
| `Proven.Handshake.hndl_resistance` (`ModelSecurity.lean`) | `Composed.Security.HNDLResistance` (`Security/Model.lean`) | Bhargavan et al. (2024), **Theorem 1 (5)** (§4, App. A) |
| `Proven.Refinement.comp_refines_cli_placed` (`Refinement.lean`) | `CompRefinesCliBinaryPlaced cliElfBytes` (`Refinement/ElfBinding.lean`) | **New** (no paper counterpart): whole-protocol ARM64 ELF trace refinement and progress, at every placement of the verified libraries |
| `Proven.Security.signal_session_secure_placed` (`Security.lean`) | `SignalSessionSecurePlaced cliElfBytes` (`Security/Binary.lean`) | **New** (no paper counterpart): all 10 security queries on ARM64 ELF traces, at every placement of the verified libraries |
| `Proven.RefinementPreservation.comp_refinement_preservation_cli` (`RefinementPreservation.lean`) | `CompRefinementPreservationCli Agree R` (`Refinement/RefinementPreservation.lean`) | **New**: generic metatheorem transferring the 10 model theorems across CLI refinement |
| `Proven.ExternWitness.comp_externsSatisfiable_cli` (`Symbolic/Tests/ExternWitness.lean`) | `CompExternsSatisfiableCli` (`Proofs/SpecLemmas/ElfBindingProofDefs.lean`, untrusted) | **New**: non-vacuity witness proving crypto extern contracts + hooks are satisfiable |

*(Model-level sanity and premise-satisfiability predicates such as `SanityHonestSession`, `SanityHonestWithOPK`, `FSPremiseSatisfiable`, and `HandshakeSecrecyPremiseSatisfiable` are additionally proved in `Symbolic/Tests/ModelNonVacuity.lean`.)*

---

## 3. Differences from Cheval et al. (2026): Double/Triple Ratchet and `DR-PQXDH*`

### 3.1 Unrestricted Composed `PQXDH ∘ SPQR ∘ Triple Ratchet` vs. Restricted `DR-PQXDH*`

In Cheval et al. (2026), full ratchet compromises were proved only for the **standalone Double Ratchet (`DR`)**, which assumes Alice and Bob begin with an idealized, pre-shared fresh root key `SK` and never models how that key was established. When Cheval et al. composed the Double Ratchet with PQXDH (`DR-PQXDH*`, §4.3, Table 1 & Table 2), ProVerif required ~7 hours and 46 GB of RAM even after imposing four major restrictions:

1. **Single session only**: At most one PQXDH handshake could execute in the entire trace.
2. **No one-time prekeys (`OPK`)**: Prekey bundles omitted `OPK_B`.
3. **No PQXDH compromises or quantum breaks**: Neither identity keys (`IK`), signed prekeys (`SPK`), Kyber prekeys (`PQSPK`), nor DH/KEM hardness could be compromised.
4. **No ratchet private-key (`DHs`) compromises**: Unlike standalone `DR`, `DR-PQXDH*` disabled `CompromiseDHs`, allowing the adversary to leak only `RK`, `CKs`, `CKr`, and skipped `MK`s.

**How our theorems differ:**
`Proven.ForwardSecrecy.forward_secrecy` and `Proven.PostCompromiseSecurity.post_compromise_security` prove Forward Secrecy and Post-Compromise Security directly on the **unrestricted composed state machine** (`DY.Libsignal.Composed.reachability` in `Specifications/Model/Composed.lean`):
- **Unbounded sessions and participants** (including dishonest identities registered via `registerCorruptIdentity`),
- **Optional one-time prekeys (`OPK`)** alongside reusable signed and Kyber prekeys,
- **All ratchet compromises enabled**, including **`ExposedDHs`** (`CompromiseDHs`) and **`ExposedSpqr`**,
- **All PQXDH compromises and breaks enabled**, including `CompromisedIK`, `CompromisedSPK`, `CompromisedPQSPK`, `CompromisedOPK`, `BrokenDH` (with discrete-log oracle `invertDH`), and `BrokenKEM` (with KEM-key inversion oracle `invertKEM`),
- **Every message from message 0 onward** is covered (including Alice's initial `PreKeySignalMessage` payload before Bob has replied).

**How the composed excuse bridge works (`HandshakeRootCompromised` and `BrokenDH`):**
If PQXDH keys can be compromised before or after a handshake, when should the ratchet consider a session's *initial* root and chain keys (`keys.rk`, `keys.ck`) already compromised? Our `mkSecurityTracePredicates` (`SecurityTracePredicates` in `Specifications/Security/Model.lean`) connects Cheval et al.'s ratchet queries to Bhargavan et al.'s handshake excuses via two exact clauses in `Compromised`:
1. `HandshakeRootCompromised tr k`: An initial handshake output `keys.rk` or `keys.ck` counts as compromised if and only if the handshake event at trace index `j` (`AliceDone` or `BobDone`) satisfies Bhargavan et al.'s **`AliceHandshakeWasCompromised`** (Theorem 7, for Alice) or **`BobHandshakeWasCompromised`** (Theorem 9, for Bob). If PQXDH protects the handshake (e.g., `IK_A` and `IK_B` are leaked *after* the handshake while `SPK_B` and `PQSPK_B` remain safe, or `DH` is broken *after* the handshake while `PQSPK_B`/Kyber holds), `HandshakeRootCompromised` is **false**, and message 0 and subsequent chains remain secret! Even if the initial handshake *is* compromised (e.g., `IK_B` was leaked before Alice initiated), **`PCSQuery` still guarantees self-healing** once Alice and Bob exchange uncompromised DH ratchet keys (provided `BrokenDH` has not occurred).
2. `honestDH k ∧ tr.EventLogged PQXDHEvent.BrokenDH`: Because `invertDH` allows a quantum attacker to compute discrete logarithms of any public ratchet key on the wire after `BrokenDH`, honest DH ratchet private keys count as compromised once `BrokenDH` is logged.

On traces satisfying Cheval et al.'s `DR-PQXDH*` restrictions (no PQXDH compromises, no `BrokenDH`, no `ExposedDHs`, single session, no `OPK`), `HandshakeRootCompromised` and `BrokenDH` are identically false, so our theorems strictly generalize Cheval et al.'s `DR-PQXDH*` rows.

### 3.2 Structural KDF-Genealogy Queries vs. Ghost Ratchet-Counter Arithmetic

**In Cheval et al. (2026) (Appendix A, Figures 3–6):**
Because ProVerif queries cannot easily recurse over arbitrary-length KDF derivation chains, Cheval et al. instrument every participant state with ghost integer counters (`r_idx` for DH ratchet epochs, `ns`/`nr` for symmetric chain positions) and a ghost session tag `session(sd, idA, idB)`. They write **four separate queries** (Sender FS, Sender PCS, Receiver FS, Receiver PCS) that characterize which compromises can affect a target message key using integer inequalities such as:
- `CompromiseRK(sd', r_idx')` with `r_idx' <= r_idx`,
- `CompromiseCKs(sd, r_idx, ns)` with `ns <= n`,
- `CompromiseDHs(sd', r_idx')` combined with an earlier `CompromiseRK`, and
- healing conditions requiring `r_idx' + 2 <= r_idx`.

*(Note: Manual counter indexing is error-prone in paper presentation — in Cheval et al.'s Appendix A, Figure 5 l. 726 writes `CompromiseMK(session(sd,idB,idA), r_idx+1, n, mk)` instead of `r_idx` on Receiver FS, and Figures 4 & 6 leave `dhs_prv'` unbound in the `CompromiseDHs` disjunct.)*

**In our Lean specifications (`DY.Libsignal.TripleRatchet.Cheval` in `Specifications/Security/Model.lean`):**
We replace counter arithmetic with **one unified `FSQuery` and one unified `PCSQuery`** (covering both `.sender` and `.receiver` `TREvent.MessageKey` events) phrased directly in terms of **cryptographic KDF genealogy** over terms:
- `DerivesMsgKey ck mk`: symmetric chain key `ck` reaches message-key seed `mk` in zero or more `kdfCk` steps (`ck = ck₀ → ck₁ → … → mk`).
- `DerivesChain rk ck`: a DH ratchet step `createChain rk peerPk ownSk` outputs chain key `ck`.
- `RootDescends rk rk'`: root key `rk'` descends from `rk` in zero or more `createChain` steps.

Using these relations:
- **`FSQuery`** states that for every message-key seed `mk` used on the trace whose hybrid message key is known to the attacker:
  1. `mk` itself was compromised (`ExposedMK` from the skipped-key cache), **or**
  2. some ancestor chain key `ck` (`DerivesMsgKey ck mk`) was compromised (`ExposedCKs`, `ExposedCKr`, or initial `HandshakeRootCompromised`), **or**
  3. some ancestor root key `rk` (`DerivesChain rk ck ∧ DerivesMsgKey ck mk`) was compromised (`ExposedRK` or initial `HandshakeRootCompromised`).
- **`PCSQuery`** states that if `mk` is derived at or after a healing DH ratchet step `(rk_heal, ck_heal) := createChain rk_prev (dhPk peerSk) ownSk` between two honest DH ratchet secrets (`HonestDH ownSk` and `HonestDH peerSk`), and the attacker knows `mk`'s hybrid message key, then either:
  1. `mk` itself was compromised, **or**
  2. an ancestor chain key `ck` (`DerivesMsgKey ck mk`) was compromised, **or**
  3. a root key **at or after the heal** (`RootDescends rk_heal rk`) that derives `mk`'s chain was compromised, **or**
  4. a root key **before the heal** (`RootDescends rk rk_prev`) was compromised **AND** at least one of the two healing DH secrets (`ownSk` or `peerSk`) was compromised (via `ExposedDHs` or `BrokenDH`).

This directly expresses the cryptographic meaning of FS and PCS without relying on partner counter synchronization.

### 3.3 Triple Ratchet and SPQR Modeling: "Cheval + Leaks" and `ExposedSpqr`

**In Cheval et al. (2026) (§4.1.4):**
Cheval et al. model the Triple Ratchet via a minimal hook: whenever a party encrypts or decrypts, the ProVerif process reads a post-quantum key directly from the attacker (`in(att, pq_mk)`) and derives `tr_mk = kdf_hybrid(dr_mk, pq_mk)`. SPQR's internal state, wire headers, initialization from PQXDH, and state compromises are omitted. This neatly proves that *classical* Double Ratchet security survives even if SPQR keys are chosen adversarially, **but** it does not model SPQR state evolution, V0 downgrade rejection, or whether leaking SPQR's stored state hurts classical keys.

**In our Lean model (`Specifications/Model/TripleRatchet.lean`, `EquationalTheory/Spqr.lean`):**
We implement a **"Cheval + leaks"** design that strictly subsumes Cheval et al.'s adversarial-salt guarantee while faithfully tracking `libsignal` v0.105.4's SPQR V1 lifecycle:
1. **Attacker-chosen salt retained (`pqSalt ← receiveMessage pqIdx`)**: Like Cheval et al., `messageEncrypt`, `messageDecrypt`, `messageDecryptSkipped`, and `bobStart` still read the `pqSalt` actually passed into `trMsgKeys` from an attacker-chosen network handle. Thus, classical FS and PCS hold even if SPQR is broken or manipulated.
2. **Real opaque SPQR V1 state (`TRState.spqr`)**: Initialized from PQXDH's third HKDF block `keys.pqr` (`spqrInit k.pqr spqrA2B` for Alice, `spqrB2A` for Bob), stepped via `spqrSend st.spqr coins` on encryption and `spqrRecv st.spqr msg.pqRatchet spqrMsgIdx` on decryption. Empty `pq_ratchet` fields (SPQR V0 downgrade attempts) are rejected by `spqrRecv`, matching `libsignal` configured with `min_version = V1`, and fresh epoch-0 chain keys agree (`spqrRecv_init_agree`).
3. **Honest SPQR keys published & `pq_ratchet` MAC-authenticated**: On every send and receive, our model publishes the computed SPQR key to the network (`sendMessage key`) and places the SPQR wire message inside `SignalMessage.pq_ratchet` under the wire MAC (`EquationalTheory/TrWireMsg.lean`). Because honest SPQR keys are on the network, an honest network can deliver the real SPQR key as `pqSalt` — making real `libsignal` runs valid traces of our model (witnessed by `SanityHonestSession` in `Tests/ModelNonVacuity.lean`) and enabling binary refinement.
4. **Full SPQR state compromise (`exposeSpqr` / `TREvent.ExposedSpqr`) excuses nothing**: Our model includes an explicit transition `exposeSpqr` that leaks `st.spqr` to the attacker, equipped with a *state transparency* attacker rule (`Spqr.attackerKnowledge`) that lets the adversary extract the underlying `keys.pqr`, coins, and nested SPQR states. Crucially, **`TREvent.ExposedSpqr` is absent from `(mkSecurityTracePredicates tr Knows).Compromised`**: leaking a party's entire SPQR state never excuses any message key in `forward_secrecy` or `post_compromise_security`.

*(Note: Because `pqSalt` is attacker-chosen and honest SPQR keys are published in `TripleRatchet.lean`, our ratchet FS/PCS theorems — like Cheval et al.'s §4.1.4 — prove the classical/hybrid non-regression guarantee of the Triple Ratchet rather than post-quantum ratchet healing after `BrokenDH`; post-quantum HNDL protection of the initial handshake keys `rk`, `ck`, `pqr` is proved in `Proven.Handshake.hndl_resistance`.)*

### 3.4 Concrete 3-Block HKDF Message Keys and `TRKeyKnown`

- **Cheval et al.** treat each message key `tr_mk` as a single atomic symmetric key.
- **`libsignal` and our model (`Specifications/Model/MsgKeys.lean`)** expand each `(pqSalt, seed)` pair via HKDF-SHA256 (`"WhisperMessageKeys"`) into three keys: a 32-byte AES-256-CBC `cipherKey`, a 32-byte HMAC-SHA256 `macKey` (whose output is truncated to 8 bytes on the wire via `EquationalTheory/Trunc.lean`), and a 16-byte `iv`.
- In `Specifications/Security/Model.lean`, `TRKeyKnown Knows seed pqSalt` holds when `Knows seed ∨ Knows (trMsgKeys pqSalt seed).cipherKey`. Knowing `cipherKey` is what breaks message confidentiality, and knowing `seed` gives `cipherKey` for every known `pqSalt`. `macKey` and `iv` are intentionally excluded from `TRKeyKnown`: `iv` reveals nothing about the plaintext, and `macKey` concerns forgery/integrity rather than secrecy (matching Cheval et al., who do not state ratchet ciphertext-authenticity theorems).

### 3.5 Omission of Header Encryption (`DR-HE`, `DR-HE*`)

Cheval et al. analyze the Double Ratchet specification's optional **Header Encryption** variants (`DR-HE`, where ProVerif proves FS in 21 hours / 232 GB RAM and runs out of memory on PCS; and `DR-HE*` without `DHs` compromises, where FS and PCS succeed). As Cheval et al. note, Signal's production `libsignal` library does **not** use header encryption (using standard `SignalMessage` headers instead). Because our theorems target `libsignal` v0.105.4, header encryption is not modeled.

### 3.6 Cheval et al.'s Three Attacks, Curve25519 Cofactor/Torsion, and Implementation Bounds

Cheval et al. (§3) analyze three attacks on the Double Ratchet spec and older versions of `libsignal`. Our model and binary specifications relate to each as follows:

1. **Null-chain-key bug in the prose Double Ratchet spec (§3.1)**:
   - *The issue*: Signal's prose DR specification initializes the responder's sending chain key `CKs` to a public constant `0` (while `libsignal` never lets Bob send before a DH ratchet step).
   - *Our model*: Matches `libsignal`. Bob's initial `recv` list is empty (`recv := []`), forcing a DH ratchet step on his first receive, and `aliceStart` derives `cksA` via `createChain` while setting `recv` to `keys.ck`. No null chain key exists.

2. **Responder weak-state forced-storage attack (`st_0`, §3.2.1)**:
   - *The issue*: Prior to `libsignal` commit `cd361186`, processing an incoming `PreKeySignalMessage` initialized a responder state `st_0` (containing `keys.rk` and Bob's medium-term `spkSk` as `dhs`) and persisted `st_0` before verifying the inner `SignalMessage` MAC — allowing an attacker to send a malformed `PreKeySignalMessage` and force Bob to keep `spkSk` in session storage indefinitely even after prekey rotation. In Cheval et al.'s `DR-PQXDH*` (§4.3 l. 627–629), responder setup was still modeled as two separate steps (storing `st_0` first, then decrypting), which is one reason `DR-PQXDH*` had to disable `SPK` and `DHs` compromises.
   - *Our model*: `Composed.bobStart` (`Specifications/Model/Composed.lean` l. 354–391) models patched `libsignal` **atomically**: `bobHandshake`, in-memory `st0` construction, `ensureReceiverChain`, `spqrRecv`, and `verifyMacAndDecrypt` all run before any event is logged, any `OPK` is marked used, or any `TRState` is stored. If MAC verification fails, nothing is stored, so `st0` can never be leaked — allowing full `SPK` and `DHs` compromises without restriction. *(A mutation-testing harness for this bug also exists in `Symbolic/BugInjection/` under `cheval26-weak-state`.)*

3. **Curve25519 small-subgroup / 8-torsion replay attack (§3.2.2)**:
   - *The issue*: In `libsignal` prior to commit `5293caa6`, `PreKeySignalMessage` replay caching indexed Alice's ephemeral `base_key` (`EK_A`) by its raw 32-byte encoding, while X25519 scalar multiplication clears the low 3 bits ("clamping"), multiplying by the cofactor 8. Adding one of Curve25519's seven non-zero 8-torsion points to `EK_A` produced different public-key bytes that yielded the *exact same* DH shared secrets and valid inner MAC, bypassing `base_key` deduplication and re-opening sessions when no `OPK` was used.
   - *Cheval et al.'s ProVerif model*: Uses standard prime-order ideal Diffie-Hellman; as noted in their §6 ("Future Work", l. 651), Curve25519 cofactor/torsion properties are **outside the scope of their ProVerif proofs**.
   - *Our Lean model & binary specs*: Explicitly model X25519's non-prime-order and encoding quirks in `EquationalTheory/X25519.lean` and `Concrete/ExternInterpretation.lean`:
     - Non-canonical 32-byte encodings (`X25519.Variant`, `variation : Fin 4` covering bit-255 flips and $u + p$ for $2^{255}-19 \le u < 2^{255}$),
     - 8-torsion point addition (`X25519.TorsionVariant`, `torsion : Fin 8`),
     - Low-order point rejection (`isLowOrderKey` / `x25519LowOrder`), and
     - `isCanonicalKey ek` in `PQXDH.bobHandshake` (matching `libsignal`'s `PublicKey::is_canonical`), reinforced at the binary extern boundary by `X25519TorsionShiftsRejected`.
   - *Subtlety on exact `PreKeySignalMessage` replays*: At the **binary CLI layer**, `signal-session` runs `libsignal`'s `.base-keys` deduplication table on Bob's last-resort Kyber prekey, rejecting exact replays. At the **symbolic model layer**, `Composed.bobStart` intentionally *omits* the `.base-keys` replay table (an over-approximation of attacker power!), allowing exact replays of a `PreKeySignalMessage` with canonical `ek` when no `OPK` was used. By binding the ghost session identifier to both the decoded ratchet key and the handshake root key (`sid := concat (normalizeX25519Key msg.ratchetKey) k.rk`), our symbolic proofs establish that FS and PCS hold *even if* exact `PreKeySignalMessage` replays create duplicate responder states.

4. **Bounded queues, integer limits, and historical snapshot leaks**:
   - Whereas ProVerif models unbounded receiver chains and unbounded message counters, `TripleRatchet.lean` models `libsignal`'s exact constants: `MAX_RECEIVER_CHAINS = 5` (evicting the oldest receiver chain), `MAX_FORWARD_JUMPS = 25000` (capping skipped-key generation per jump), `u32::MAX` counter-overflow guards, and seed-only skipped-key caching (`SkippedKeyStored` caches `seed` before `spqrRecv`, running `spqrRecv` when the skipped message actually arrives).
   - Moreover, in our symbolic model, `exposeKey` and `exposeSpqr` can leak **any historical `TRState` snapshot** ever stored on the trace (modeling imperfect memory erasure / backup snapshots), not just the latest cell. (At the binary refinement layer, `KeyInDir` / `KeyInRecord` reads secrets from the party's current on-disk `SessionRecord`.)

---

## 4. Differences from Bhargavan et al. (2024): PQXDH Handshake Theorems

### 4.1 Symbolic Scope Only (Computational Theorems 2–6 Not Replicated)

Bhargavan et al. present two families of results:
- **Symbolic ProVerif theorems**: **Theorem 1** (§4, five high-level properties) derived from **Theorems 7, 8, and 9** (Appendix A), which characterize exact security under arbitrary dynamic compromises of `IK_A`, `IK_B`, `SPK_B`, `PQSPK_B`, `OPK_B`, plus dynamic `BrokenDH` and `BrokenKEM` events.
- **Computational CryptoVerif theorems**: **Theorems 2–6** (§5), which prove computational key indistinguishability, authentication, classical GapDH security, post-quantum Kyber security, and semi-honest collision resistance (`SH-CR`) of Kyber — **but** under a much more restricted compromise model in which only long-term identity keys (`IK`) can be dynamically compromised (prekeys `SPK`, `PQSPK`, `OPK` are never dynamically leaked in their CryptoVerif models).

Our Lean theorems in `Symbolic/Theorems/ModelSecurity.lean` correspond to **Theorem 1 and Appendix A Theorems 7–9** (the full dynamic prekey/identity/quantum-break symbolic threat model), lifted into the composed `PQXDH ∘ SPQR ∘ Triple Ratchet` protocol and refined to the ARM64 binary. We do not formalize computational game-hopping reductions (Theorems 2–6).

### 4.2 Whole-Protocol Composition, 3-Block Handshake Output (`rk`, `ck`, `pqr`), and `SessionStateExposed`

- **In Bhargavan et al. (2024)**: PQXDH derives a single symmetric key `SK` and immediately uses `SK` to AEAD-encrypt a constant `"hello"` confirmation payload with associated data `IK_A ‖ IK_B` (plus `PQSPK_B` in Revision 2). No session state is stored after the handshake.
- **In `libsignal` v0.105.4 and our composed model (`PQXDH.lean`, `Composed.lean`)**:
  1. `pqxdhKdf` (`"WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024"` over `0xFF^32 ‖ DH1 ‖ DH2 ‖ DH3 ‖ [DH4] ‖ ss`) outputs **three 32-byte blocks**: `HandshakeKeys = { rk, ck, pqr }`, which seed the Triple Ratchet root key, initial chain key, and initial SPQR V1 authenticator key.
  2. Key confirmation on Bob's side (`bobStart`) is performed not by a standalone `"hello"` AEAD tag, but by decrypting and verifying the 8-byte truncated HMAC-SHA256 of Alice's initial Triple Ratchet `SignalMessage` (which authenticates `serializedIk` of both parties, the ratchet header, the AES-256-CBC ciphertext, and the SPQR V1 `pq_ratchet` payload, salted with SPQR).
  3. **Per-block `SessionStateExposed` excuse (`Specifications/Security/Model.lean`)**: Because a completed handshake initializes a persistent Triple Ratchet session whose state can later be leaked by the adversary (`exposeKey`, `exposeSpqr`), an unguarded claim `¬ Knows k` would trivially fail whenever the user later leaks their session file! Our five handshake secrecy theorems (`AliceInitiatorSecrecy`, `BobResponderSecrecy`, `HandshakeForwardSecrecy`, `SessionIndependence`, `HNDLResistance`) quantify over each individual block `k ∈ {keys.rk, keys.ck, keys.pqr}` (`IsHandshakeBlock keys k`) and excuse `Knows k` if either:
     - Bhargavan et al.'s PQXDH compromise disjunction holds (`AliceHandshakeWasCompromised` for Alice, `BobHandshakeWasCompromised` for Bob), **or**
     - **`SessionStateExposed tr keys k`** holds — meaning **that specific block `k`** was directly leaked from a Triple Ratchet session started by that handshake:
       - `keys.pqr` via `TREvent.ExposedSpqr` (since `pq_ratchet_state` stores `pqr`),
       - `keys.ck` via `TREvent.ExposedCKr` or `TREvent.ExposedCKs` (before the initial chain advances), or
       - `keys.rk` via `TREvent.ExposedRK` (if Bob's initial root key were exposed; Alice immediately ratchets `keys.rk` in `aliceStart`).
     - **Block isolation**: Exposing one block *never* excuses any other block! For instance, leaking `pqr` via `ExposedSpqr` does not allow the attacker to learn `keys.rk` or `keys.ck`, and leaking ratcheted keys after symmetric/DH steps does not excuse unexposed handshake blocks.

### 4.3 Symbolic KEM Public-Key Binding (`SH-CR`) vs. Putting `PQSPK_B` in `AD`

One of Bhargavan et al.'s central discoveries (§4.1.2) is the **KEM re-encapsulation attack**:
- Suppose a generic KEM allows an attacker who knows a compromised secret key `pqsk₁` to decapsulate Alice's ciphertext `ct₁` into shared secret `ss`, and then re-encapsulate that *exact same* `ss` under a different honest Kyber prekey `pqpk₂` of Bob. If `PQSPK_B` is not bound into the key derivation or associated data `AD`, Alice and Bob derive identical session keys while disagreeing on `PQSPK_B` (`pqpk₁` vs. `pqpk₂`), breaking `PQSPK_B` agreement in Theorem 8 and violating session/state isolation.
- **How Bhargavan et al. handled this**:
  - Their **ProVerif** symbolic KEM modeled encapsulation as generic public-key encryption of a fresh secret (`aenc(ss, pk)`), which permits re-encapsulation. Consequently, their ProVerif proofs analyzed **PQXDH Revision 2**, which modifies the protocol to append `PQSPK_B` to the AEAD associated data `AD` (§4.2, l. 423).
  - However, **`libsignal` did not add `PQSPK_B` to the `SignalMessage` associated data** (Bhargavan et al., §5.3, l. 441, 453). Instead, Bhargavan et al. proved in **CryptoVerif** (Theorems 5 & 6) that `libsignal` is secure without changing `AD` because Kyber-1024 (and FIPS 203 ML-KEM) hashes `H(pk)` into `ss` inside the Fujisaki-Okamoto transform, satisfying **semi-honest collision resistance (`SH-CR`)**.
- **How our Lean symbolic model handles this (`Specifications/Model/EquationalTheory/Kem.lean`)**:
  - Because our symbolic model refines down to the real `libsignal` v0.105.4 binary (whose `SignalMessage` MAC covers `myIk`, `peerIk`, and the protobuf wire message, *not* `PQSPK_B`), we build `SH-CR` **directly into the symbolic KEM term algebra**:
    ```lean
    kemEncap pk entropy = (Encap{pk, entropy}, SharedSecret{pk, entropy})
    ```
  - Because `SharedSecret` algebraically carries `pk`, a shared secret encapsulated to `pqpk₁` can never equal a shared secret encapsulated to `pqpk₂ ≠ pqpk₁` — even after `BrokenKEM` (which unlocks `kemPkInvert` to extract secret keys, modeling a break of module-LWE hardness rather than a break of SHA-3/SHAKE random oracles). This captures `libsignal`'s actual defense symbolically and proves Theorem 8's `pqpk` agreement without modifying `AD`.
  - **Implicit rejection**: Real Kyber decapsulation returns a pseudorandom rejection key on malformed ciphertexts rather than an error. In `Kem.lean`, symbolic `kemDecap` returns `none` on non-matching ciphertexts; at the binary refinement layer, the negligible possibility that a concrete implicit-rejection key accidentally passes Bob's 8-byte MAC check on a fresh base key is explicitly captured inside `CollisionAfterExplainedPrefix` (`BobSessionStartCollidesOrImplicitRejectsOn` / `ImplicitReject` gated by `FreshBaseKey` and `TrialMacMatches`).

### 4.4 Formal Clarifications and Precision Fixes in Theorems 7, 8, 9, and Theorem 1

Translating Bhargavan et al.'s prose statements (Appendix A, l. 678–713) into machine-checked Lean required resolving five subtle ambiguities and formalization details:

1. **"Some `SPK_B`" means the *session's* `spk`, not an arbitrary unrelated `SPK` of Bob**:
   - In Appendix A prose, Theorem 7 (case 2), Theorem 8 (case 2), and Theorem 9 (case 2) write *"some $\mathsf{SPK}_B$ was compromised"*. Reading this literally as `∃ spk', CompromisedSPK b spk'` would mean compromising *any* old/unrelated signed prekey of Bob excuses breaking a session that used a completely different `spk` — which would make **Theorem 1's Session Independence corollary unprovable**!
   - Matching Bhargavan et al.'s own ProVerif query for Theorem 7 (App. A, l. 662: `event(CompromiseSPK(B, spk))` bound to `AlexOK(A, B, spk, pqpk, ts)`), our `AliceHandshakeWasCompromised`, `HandshakeAuthWasCompromised`, and `BobHandshakeWasCompromised` bind `CompromisedSPK b spk` to **the target session's `spk`**. This makes `Proven.Handshake.session_independence` derivable directly from `alice_initiator_secrecy` and `bob_responder_secrecy`.

2. **Typo fix in Theorem 9 Case 3 (`A` vs. `B`)**:
   - Bhargavan et al. (App. A, l. 700) write: *"$\mathsf{IK}_B$, $\mathsf{SPK}_B$ and $\mathsf{PQSPK}_B$ are compromised after the communication, and either no $\mathsf{OPK}$ was used or it was compromised. (all secret material of $A$ is leaked here...)"*. As the listed keys are all $B$'s (Blake / our Bob), "material of $A$" is a typo for $B$; `BobHandshakeWasCompromised` formalizes the four listed compromises on Bob `b`.

3. **Peer-name quantification (`∃ b'`) in Theorem 8 under `IK_B` compromise (Duplicate-Key / Unknown Key-Share)**:
   - Theorem 8 (and Theorem 1's KCI resistance) guarantees authentication of Alice `a` to Bob `b` **even when Bob's own identity key `IK_B` is compromised** (`CompromisedIK b ikB` is not in `HandshakeAuthWasCompromised`).
   - However, once `IK_B` is leaked, the attacker can call `registerCorruptIdentity c ikB_sk` to register a *different* participant name `c ≠ b` in the PKI with Bob's stolen identity key (standard PKIs do not check global key uniqueness across names). Alice `a` can then initiate a session with `c` (`AliceDone a c ikA ikB spk pqpk ...`) using Bob's genuine prekeys (whose signatures verify under `vk ikB`), and Bob `b` will accept the resulting message from `a` (`BobDone b a ikB ikA spk pqpk ...`) because `libsignal`'s MAC binds **serialized identity public keys** (`serializedIk`), not string names!
   - Requiring `AliceDone a b ...` (with `b' = b`) would therefore be **false** on reachable traces! Notably, Bhargavan et al.'s prose in Theorem 8 says *"there exists a responder Alex that also accepted ... with the same $\mathsf{SPK}_B$ and $\mathsf{PQSPK}_B$"* without claiming Alex intended peer name `B`. Our `ResponderSessionAgreement` (`Specifications/Security/Model.lean`) pins Alice (`a`), causal order (`j < i`), and `pqpk`, while quantifying `∃ b'` over Alice's intended peer name.

4. **Prekey agreement up to X25519 u-coordinate re-encoding (`SameDHKey`, `SameOPK`)**:
   - Because X25519 ignores bit 255 and reduces $u \bmod (2^{255}-19)$, an attacker can always re-encode an unsigned `OPK_B` on the wire (and, when `IK_B` is compromised, can also re-sign a re-encoded `SPK_B`) without changing any DH shared secret. Requiring syntactic equality `spk = spk'` and `opk = opk'` in Theorem 8 would fail on such benign re-encodings. Our `ResponderSessionAgreement` (and `SIPremise`) compares X25519 public keys via `SameDHKey` and `SameOPK` (`X25519.normalizeX25519Key`), mirroring the computational caveat in Bhargavan et al.'s Theorem 2 (*"modulo the subgroup elements of X25519"*).

5. **Explicit type-byte domain separation (§4.1.1) and formal derivation of Theorem 1**:
   - To rule out Bhargavan et al.'s **public-key confusion attack** (§4.1.1, where an attacker tricks a client into verifying an EC signature as a KEM signature or vice versa), `PQXDH.lean` models `libsignal`'s `0x05` (`encodeEC`) and `0x08` (`encodeKEM`) serialization type bytes explicitly.
   - Whereas Bhargavan et al. justify the five properties of Theorem 1 via short prose remarks in Appendix A (l. 708–713), `Symbolic/Theorems/ModelSecurity.lean` states and proves all five (`peer_authentication`, `handshake_forward_secrecy`, `kci_resistance`, `session_independence`, `hndl_resistance`) as machine-checked Lean corollaries of `alice_initiator_secrecy`, `bob_responder_secrecy`, and `authentication`. *(For `hndl_resistance`, `HNDLQuery` states the secrecy half on `AliceDone` and `BobDone`; the authentication half under post-handshake `BrokenDH` is already verbatim `AuthenticationQuery`, since every clause of `HandshakeAuthWasCompromised` requires `j < i`.)*

---

## 5. Beyond Both Papers: ARM64 Binary Refinement and Its Scope Differences

### 5.1 What `comp_refines_cli_placed` and `signal_session_secure_placed` Prove (`Symbolic/Theorems/Refinement.lean`, `Symbolic/Theorems/Security.lean`)

Neither Bhargavan et al. nor Cheval et al. verify source code or compiled machine code; any discrepancy between a paper's ProVerif model and `libsignal`'s Rust/assembly implementation (such as protobuf parsing edge cases, integer overflows, unvalidated curve points, non-atomic session writes, or file-system state corruption) lies outside their proofs.

In `Symbolic/Theorems/Refinement.lean` and `Symbolic/Theorems/Security.lean` (built in the `CliElfLib` Lake target), we prove two end-to-end theorems over **`cliElfBytes`** — the SHA-256-pinned static musl ARM64 ELF binary `libsignal-cli` (`2f20c836342437a882b5882c34eab604e4f23b2b388c2b2a0696eeda51cddc7e`, pinned in `LibsignalBinary/Specifications/SignalSession/CliElf.lean`) compiled from `libsignal` v0.105.4:

1. **`Proven.Refinement.comp_refines_cli_placed : CompRefinesCliBinaryPlaced cliElfBytes`**:
   - For every pair of placements `mpl`, `mmpl` at which `libsignalSessionLib` and `VerifiedLibraries.mallocngLib` are linked into `cliElfBytes` (`LinkedAt`; non-vacuous by `libsignal_cli_elf_linked_in` and `libsignal_cli_elf_mallocng_linked_in`), the image's code matches the verified libraries (`CliElfCodeMatchesPlaced`).
   - The ELF bytes parse cleanly into an ARM64 `ElfImage`, and every guarded CLI call (`ValidCall`, `InputsFor`) at a reachable turn (`CliReachable`) terminates with a concrete process outcome (`CliElfProgressPlaced`: `cliRunPlacedSig mpl mmpl elf W i ≠ none`, ruling out CPU faults, unhandled traps, and non-termination).
   - Across arbitrary multi-call CLI schedules (`CliTraces` in `Specifications/Refinement/Statement.lean`) of `init`, `send`, and `recv` (`CliEvent.run`) interleaved with session deletion (`clearSession`) and environment events (`CliEvent.env`: secret `.leak` events from `KeyInDir` plus dynamic `.breakDH`, `.breakKEM`, `.invertDH`, and `.invertKEM` events guarded by `InvertsGuarded`) executed by the ARM64 ISA semantics (`elfRelPlaced mpl mmpl elf`), **every concrete CLI event trace `evs : List CliEvent`** either:
     - is **explained** 1-for-1 (`Explains` in `TraceExplanation.lean`: matching each `RunEvent` to a party step via `RunMatches` or rejection `RunRejected`, with random draws sliced directly as a prefix of `ev.coins` via `GhostWF`, and each `EnvEvent` to its model compromise/exposure/break/invert step via `EnvMatches`) by a faithful run of our composed symbolic model (`ModelTraces.Step`, mirroring all 23 `Composed.reachability` transitions), **or**
     - has an explained prefix followed by an input that triggers an unavoidable **concrete cryptographic byte collision** (`CollisionAfterExplainedPrefix`).
   - What runs as **real ARM64 machine code**: CLI file I/O, protobuf wire encoding/decoding (`SignalMessage`, `PreKeySignalMessage`, `SessionRecord`, prekey records), HKDF-SHA256 structure, Double Ratchet chain management and skipped-key caching, PQXDH key-schedule assembly, and SPQR V1 state-machine logic.
   - What is **hooked at link boundaries (`HooksMatchInterpretation` & `ExternContractsHoldCli`)**: the `37` rows of `cliHookTablePlaced` (canonical list in `Computational/docs/TRUSTED_BASE.md` §5) — low-level cryptographic primitives (SHA-256 block compression, AES-256-CBC encryption and decryption as whole functions, including CBC chaining and PKCS#7 padding/unpadding, X25519 scalar multiplication, Kyber-1024 encapsulate/decapsulate, Ed25519 curve ops & torsion check, SPQR's incremental ML-KEM-768, and `libcrux_hmac`), `core::fmt::write` and `alloc::fmt::format::format_inner` (kept hooked in this release by design), the two 0-allocation write functions (`write_file`, `write_stdout`, linked in `lib1_0.o` and intercepted at entry as trusted hooks, DEV-CLI19), and the other non-crypto rows not yet de-hooked (`memmove`, `bcmp`, `strlen`, `core::slice::memchr::memrchr`, `core::str::converts::from_utf8`, `SystemTime::duration_since`, `<SystemTime as Add<Duration>>::add`, `subtle::black_box`, and the `2` X25519 `Drop::drop` zeroize hooks). **`Proven.ExternWitness.comp_externsSatisfiable_cli`** proves that a concrete `ExternInterpretation` and `CliHooks` witness simultaneously satisfies `ExternInterpretationTotalOnUsedSymbols`, `ExternContractsHoldCli` (`ExternCryptoLawsHold` + `X25519TorsionShiftsRejected`), and `HooksMatchInterpretation`, ensuring the binary theorems are never vacuous.
   - **No allocation-success assumption**: If a dynamic memory allocation fails and the binary aborts mid-call, `CliTraces.stop` terminates the trace cleanly (preserving prior leaks and the aborted `RunEvent` without allowing subsequent calls to read a half-written directory). The 5 Rust global-allocator entry points (`mallocng`), `read_file`, and `read_stdin` execute real linked ARM64 code, with per-call closedness of `fds ≥ 3` proved in `VmPreserved` (`FdsHiFrame`) and the ghost-to-real transfer proved on the K route (`ElfSlicesPqOomH2KM1.h2k_ghostArms_closed`).

2. **`Proven.Security.signal_session_secure_placed : SignalSessionSecurePlaced cliElfBytes`** (via `comp_refinement_preservation_cli`):
   - Transfers **all ten whole-trace security queries** (`AllSecurityQueriesHoldOnHwTrace` in `Security/AsmSecure.lean`) directly onto hardware traces `evs`, evaluated against the **hardware attacker's Dolev-Yao closure `HwAttackerKnows`** (seeded by public setup messages `setupSent r` and matched `.send`, `.recv`, and `.leak` visible entries — including secrets yielded by `.invertDH`/`.invertKEM` via `invertEntry` — while excluding honest plaintexts `.pt`, internal `.rng` draws, and `.accept` outputs):
     - Cheval et al.'s `FSQuery` and `PCSQuery` (over `mkSecurityTracePredicates`),
     - Bhargavan et al.'s `AliceInitiatorSecrecyQuery` (Thm 7), `BobResponderSecrecyQuery` (Thm 9), `AuthenticationQuery` (Thm 8), and
     - all five Theorem 1 corollaries (`PeerAuthenticationQuery`, `ForwardSecrecyQuery`, `KCIQuery`, `SessionIndependenceQuery`, `HNDLQuery`).

### 5.2 Why Binary Theorems Include `CollisionAfterExplainedPrefix`

In a pure symbolic model, distinct algebraic terms never collide. On concrete fixed-width byte strings (such as 32-byte SHA-256 digests or `libsignal`'s 8-byte truncated `SignalMessage` MAC), an adversary always has a non-zero (though cryptographically tiny, e.g., $2^{-64}$ for an online MAC forgery) chance of guessing a valid tag or triggering a hash/cipher collision on bytes that no symbolic step could produce. `CollisionAfterExplainedPrefix` (`NextEventCollides` in `Refinement/Statement.lean` & `TraceExplanation.lean`) collects the exact concrete byte-level anomalies that excuse a binary trace from symbolic explanation:
- **`MemoCollisionOn`**: two distinct symbolic terms evaluate under concretization `γ` to the exact same concrete byte string, or the attacker guesses an unrevealed random/derived value's bytes (including 32-byte KEM encapsulations under `kyberEncapsSymbol`).
- **`MacTagForgeryOrCollision` (`RecvCollisionOn` / `ReselectCollisionOn` / `SignalMsgAcceptedOnlyViaCollision`)**: a forged or mismatched message passes the 8-byte `SignalMessage` MAC check under an unknown seed or collides across receiver trials.
- **`BobSessionStartCollidesOrImplicitRejectsOn` (`bobTrials` gated on `libsignal`'s pre-MAC handshake guards, and `KyberMismatch`)**: on a pre-key message satisfying `libsignal`'s pre-MAC handshake guards (canonical non-low-order `baseKey`, inner `SignalMessage` version 4, non-low-order `ratchetKey`, and unused one-time prekey if named), Bob's candidate handshake trial terms (modeling Kyber-1024 implicit rejection via `PQKem.kemRejKey`) hit `MemoCollisionOn` or `MacTagForgeryOrCollision`, or concrete Kyber decapsulation disagrees with encapsulation on an honest ciphertext.

### 5.3 Important Scope Differences at the Binary Layer vs. Our Symbolic Model

While our **Symbolic Model Layer (`Security/Model.lean`)** removes the scenario and compromise restrictions of Cheval et al.'s `DR-PQXDH*` and keeps the full multi-party / quantum-break generality of Bhargavan et al., our **ARM64 Binary Layer (`Security.lean`, `Refinement.lean`)** scopes executions to the concrete `signal-session` CLI harness (`CliSetup.lean`, `Statement.lean`, `ModelTraces.lean`). Readers comparing the binary theorems against the symbolic theorems and papers should note five explicit scope details:

| Aspect | Our Symbolic Model (`ForwardSecrecy`, `PCS`, `Handshake`) | Our ARM64 Binary Theorems (`comp_refines_cli_placed`, `signal_session_secure_placed`) |
|---|---|---|
| **1. Participants & PKI** | Unbounded honest and attacker-registered corrupt participants (`registerCorruptIdentity`) | **Two fixed honest parties** (`r.alice ≠ r.bob`) provisioned in `initDirs` with pinned peer identity keys (`identities/<peer>`, `D6(a)` — modeling verified safety numbers rather than trust-on-first-use; `EnvEvent.registerCorrupt` is declared as a future placeholder not yet emitted by `CliTraces`). |
| **2. Prekey multiplicity** | Unbounded `SPK`s, `PQSPK`s, and `OPK`s per party | **1** signed prekey, **1** reusable last-resort Kyber-1024 prekey, and **0 or 1** one-time prekey (`r.withOpk`). *(Thus at the binary layer, `SessionIndependenceQuery` exercises leaking an unused `OPK` vs. sessions not using it, whereas the symbolic model exercises arbitrarily many `SPK`/`PQSPK`/`OPK` records.)* |
| **3. Quantum / cryptanalytic breaks (`BrokenDH`, `BrokenKEM`)** | **Included**: dynamic `breakDH` + `invertDH` and `breakKEM` + `invertKEM` on arbitrary keys at any point on the trace | **Included (`CliTraces.breakInvert` + `InvertsGuarded`)**: the environment dynamically emits `.breakDH` / `.breakKEM` and subsequently inverts any `HonestDHSecret` (setup DH keys or exit-0 `coins` X25519 keys) or Bob's `kyberSecB` — making **HNDL (`HNDLQuery`) a live property of the ARM64 binary**. |
| **4. Initiator/responder direction & bundles (`ValidCall`)** | Any party can initiate or respond; when `IK_B` is leaked, the server can forge arbitrary `SPK`/`PQSPK` bundles | **Fixed roles (`DEV-C-ROLES`)**: `r.alice` runs `init`, `r.bob` runs pre-key `recv`, and either party runs `send` / whisper `recv` (with re-initiation via `clearSession`). **Honest signed bundle (`HonestBundleFiles` / `DEV-PQS-BUNDLE`)**: if `init` parses a flat bundle directory (`BundleFilesFlat`), its `IK_B`, `SPK_B`, `PQSPK_B`, and signatures match Bob's provisioned files (the unsigned `one-time-pre-key` remains unconstrained and may be omitted or forged by the server). |
| **5. Wire `pq_ratchet`, multi-session `SessionRecord`, and concrete sizes** | Arbitrary attacker terms for `pq_ratchet`; unbounded concurrent sessions and historical snapshot leaks; unbounded message counts | **`PqFromHonest` (`DEV-TR-SPQR-MSG`)**: received messages carry a `pq_ratchet` payload from an earlier honest `send`. **`BobCallAllowed` (`D2(c)`)**: if Bob accepts a non-matching `PreKeySignalMessage` while already holding a session (`PreKeyNoMatch` / `¬ EligibleForSessionPromotion`, creating a 2-session `SessionRecord`), Bob makes no further CLI calls until `clearSession` (though his current session may still be leaked via `KeyInDir`). **Size & path bounds**: `< 2^32 - 1` sends (`DEV-TR-NS`), directory files `< 2^31` B (`FilesBounded`), loader-admissible input paths & file sizes (`FilesVisible`: no `.`, `stdioPaths`, leading `/`, or `..`, and `≤ MAX_LFS_FILESIZE`), stdin `< 2^32` B (`< 2^32 - 2048` B for pre-key inner messages). |

---

## 6. Reference Matrix: Every Lean Theorem vs. Paper Theorems

| Lean Theorem | Paper Counterpart | Where Our Theorem Is Stronger / More General | Where Our Theorem Is Different or Narrower |
|---|---|---|---|
| `Proven.ForwardSecrecy.forward_secrecy` | Cheval et al. (2026) Table 2 (`DR-PQXDH*` FS) & §4.1.4 | Full `PQXDH ∘ SPQR (V1) ∘ TR` with **unbounded sessions**, **`OPK`s**, **`ExposedDHs`**, **all PQXDH compromises & `BrokenDH`/`BrokenKEM`**, **stateful SPQR + `ExposedSpqr`** (excusing nothing), X25519 torsion/encoding theory, `libsignal` bounds, historical snapshot leaks, unified KDF-genealogy query; refined to ARM64 ELF in `signal_session_secure_placed`. | Targets `libsignal` v0.105.4 (no `DR-HE` header encryption). Secrecy defined on `seed` or `cipherKey` (`TRKeyKnown`, excluding `macKey`/`iv`). Binary transfer adds CLI scope (§5.3) + `CollisionAfterExplainedPrefix`. |
| `Proven.PostCompromiseSecurity.post_compromise_security` | Cheval et al. (2026) Table 2 (`DR-PQXDH*` PCS) & §4.1.4 | Same generalizations as `forward_secrecy`: heals even from excused PQXDH handshakes once honest DH ratchet keys are exchanged; `ExposedDHs` and `ExposedSpqr` fully enabled; refined to ARM64 ELF in `signal_session_secure_placed`. | Same as `forward_secrecy`: classical/hybrid ratchet healing (attacker-chosen `pqSalt`, so `BrokenDH` compromises DH ratchet keys); no `DR-HE`. |
| `Proven.Handshake.alice_initiator_secrecy` | Bhargavan et al. (2024) **Theorem 7** (App. A) | Proven inside full **composed `PQXDH ∘ SPQR ∘ TR`** (not standalone 1-message PQXDH); checks **each block `rk`, `ck`, `pqr` individually** with isolated `SessionStateExposed`; models `libsignal`'s actual `AD` via symbolic KEM `SH-CR` binding (`SharedSecret{pk, entropy}`); pins `spk` to the session's `spk`; refined to ARM64 ELF. | Symbolic Dolev-Yao (no CryptoVerif game-hopping reduction in `Symbolic/`). Implicit Kyber rejection modeled as `none` symbolically and via `ImplicitReject` in `CollisionAfterExplainedPrefix`. |
| `Proven.Handshake.authentication` | Bhargavan et al. (2024) **Theorem 8** (App. A) | Proven inside full **composed `PQXDH ∘ SPQR ∘ TR`** with `libsignal` `SignalMessage` + SPQR V1 confirmation; models X25519 encoding equivalence (`SameDHKey`, `SameOPK`) and 8-torsion rejection; handles duplicate-key PKI registration (`∃ b'` in `ResponderSessionAgreement`); refined to ARM64 ELF. | Symbolic Dolev-Yao; authentic PKI (TOFU first-contact out of scope, matching Bhargavan et al.). |
| `Proven.Handshake.bob_responder_secrecy` | Bhargavan et al. (2024) **Theorem 9** (App. A) | Proven inside full **composed `PQXDH ∘ SPQR ∘ TR`**; per-block `rk`/`ck`/`pqr` secrecy with `SessionStateExposed`; fixes paper's `A`→`B` typo in case 3 and `spk` session binding in case 2; atomic `bobStart` avoids weak-state `st_0`; refined to ARM64 ELF. | Symbolic Dolev-Yao (no CryptoVerif game-hopping reduction in `Symbolic/`). |
| `Proven.Handshake.peer_authentication`, `handshake_forward_secrecy`, `kci_resistance`, `session_independence`, `hndl_resistance` | Bhargavan et al. (2024) **Theorem 1 (1–5)** (§4, App. A) | Mechanically stated and proved as formal whole-trace corollaries of Theorems 7–9 on the composed protocol, with per-block `SessionStateExposed`; **including live HNDL (`breakDH`/`invertDH`) on the ARM64 ELF** via `signal_session_secure_placed`. | At the binary CLI layer (unlike the symbolic model layer), Bob has 1 `SPK` + 1 `PQSPK` + 0/1 `OPK` (`SessionIndependenceQuery`) and 2 honest provisioned parties without `.registerCorrupt`. |
| `Proven.Refinement.comp_refines_cli_placed` & `Proven.Security.signal_session_secure_placed` (with `comp_refinement_preservation_cli`, `comp_externsSatisfiable_cli`) | *None* (neither paper verifies source or binary code) | Machine-checked refinement and assembly-level security of the SHA-256-pinned compiled ARM64 `signal-session` ELF (`cliElfBytes`), covering `.leak` and `.breakDH`/`.breakKEM` events with no allocation-success assumption (real linked `mallocng` allocator and `read_file`/`read_stdin` code transferred via per-call `FdsHiFrame` in `VmPreserved` and the K-route proof `ElfSlicesPqOomH2KM1.h2k_ghostArms_closed`) and proved extern-contract satisfiability. | Scoped to 2 provisioned parties, CLI environment guards (`DEV-C-ROLES`, `DEV-PQS-BUNDLE`, `DEV-TR-SPQR-MSG`, `D2(c)`, `< 2^32 - 1` sends), hooked crypto externs (`HooksMatchInterpretation`), and `CollisionAfterExplainedPrefix`. |

# Glossary

Terms you meet in the computational proof of libsignal's 1:1 session, grouped by origin. ACD19 =
Alwen, Coretti, Dodis, "The Double Ratchet: Security Notions, Proofs, and Modularization for the
Signal Protocol" (ePrint 2018/1037, version 2020-02-21).

## 1. ACD19 notation and its Lean names

| ACD19 | Meaning | Lean |
|---|---|---|
| SM | secure messaging (§3) | `SMScheme`, `SM.*` |
| CKA | continuous key agreement (§4.1), the public-key ratchet | `CKAScheme`, `CKA.*` |
| FS-AEAD | forward-secure authenticated encryption with associated data (§4.2), one session per epoch | `FSAEADScheme`, `FSAEAD.*` |
| PRF-PRNG | pseudorandom function / pseudorandom number generator with input (§4.3), the root key derivation | `PRFPRNG`, `rootPRNG` |
| AEAD, OT-CCA | authenticated encryption with associated data; one-time chosen-ciphertext security (Def. 2) | `AEADScheme`, `otccaAdvantage` |
| PRG, PRF | pseudorandom generator (Def. 5), pseudorandom function | `PRGScheme`, `prfAdvantage` |
| `Δ_SM`, `Δ_CKA` | healing delay of the SM scheme, of the CKA; Thm 6: `Δ_SM = 2 + Δ_CKA` | the argument `Δ`; `2 + 1` in the statement |
| `q`, `q_ep` | number of oracle queries, number of epochs (Def. 8) | `q`, `qep` |
| `t*`, `t*_L` | attacked epoch; last leaked epoch before it | sums over `t`, `tL ∈ admissibleLastLeakGuesses Δ t` |
| `t_heal` | `t*_L + 2`, the CKA challenge epoch (fn. 13) | `healEpoch` |
| `γ`, `σ_root`, `v[t]` | CKA state, root PRF-PRNG state, FS-AEAD session of epoch `t` (Fig. 8) | `PartyState` fields |
| `T_cur`, `λ` | current CKA message; its initial value | `lam` |
| `ℓ_prv` | number of messages of the previous sending epoch (Fig. 8 header) | not modelled (DEV-SM11); libsignal's `previous_counter` (DEV-LS13) |
| `transmit-P`, `chall-P`, `deliver-P`, `inject-P`, `corr-P` | the Fig. 2 oracles | `transmitImpl`, …; restricted game `transmitR`, `corrR`, … |
| `ep-mgmt`, `sam-if-nec`, `safe-ch`, `safe-inj` | Fig. 2 helpers | `GameState.epMgmt`, `samIfNec`, `safeCh`, `safeInj` |
| `tL`, `comp`, `trans`, `chall` | Fig. 2 game state | `SM.GameState` fields |
| H0, H1, H2, H3,i | App. A hybrids: Fig. 2; without the correctness win; without injections; challenges up to epoch `i` replaced | `Config.full`, `.h1`, `.h2`, `.h3 i` (index shifted by one, DEV-SM19) |
| B1, B2, B3(,i) | ACD19's reduction adversaries | `Thm1.challSim`, `Thm1.privRed`, `redCKAAuth`, … |
| FS-Init-S, FS-Send, FS-Rcv, FS-Max, FS-Stop | FS-AEAD algorithms (Def. 14) | `FSAEADScheme` fields; FS-Max, FS-Stop not modelled (DEV-FS11) |
| P-Init, P-Up | PRF-PRNG algorithms (Def. 16) | `PRFPRNG.init`, `.up` |
| CKA-S, CKA-R | CKA algorithms (Def. 12) | `CKAScheme.send`, `.receive` |

### PQXDH and Fiedler–Günther (FG24) notation and its Lean names

| Paper | Meaning | Lean |
|---|---|---|
| `IK_A`, `IK_B` | initiator and responder Curve25519 identity keys | `ikAPk`/`ikASk`, `ikBPk`/`ikBSk` (and signing half `ikSignPk`/`secIKAsign` in `PrincipalEntry`, verified against `ikB` in `PreKeyBundleInput` under the two-key idealization in `SignalPqxdh.Game`) |
| `EK_A`, `eph_A` | initiator ephemeral base key and initial Double Ratchet sender key | `ekAPk`/`ekASk`, `ephAPk`/`ephASk` |
| `SPK_B`, `OPK_B` | responder signed pre-key and optional one-time pre-key (Curve25519) | `spkPk`/`spkSk`, `opkPk?`/`opkSk?` |
| `PQSPK_B` | responder Kyber1024 pre-key | `pqspkPk`/`pqspkSk` (`kpkPub`/`kpkSec` in `ResponderPreKeySecrets` and `PreKeyBundleFields`) |
| `DH1`, `DH2`, `DH3`, `DH4` | X25519 legs `DH(IK_A, SPK_B)`, `DH(EK_A, IK_B)`, `DH(EK_A, SPK_B)`, and optional `DH(EK_A, OPK_B)` | `dh1`, `dh2`, `dh3`, `dh4` in `SignalPqxdh.Model.initiateKeys` / `acceptKeys` |
| `CT`, `SS` | Kyber1024 ciphertext and 32-byte shared secret | `kemCt`, `kemSs` |
| `KM` (`ikm`) | `0xFF^32 ‖ DH1 ‖ DH2 ‖ DH3 [‖ DH4] ‖ SS` | `buildSecrets` |
| `SK` (`DRKey`) | 96-byte `HKDF-SHA256(None, KM).expand(INFO_PQXDH, 96)` split into `(rk, ck, pqr)` (root key, chain key, SPQR ratchet key) | `DRKey` (`DRKey.rootKey`, `DRKey.chainKey`, `DRKey.pqrKey` in `SignalPqxdh.Model`) |
| `AD` | first-message associated data `0x05 ‖ ikA ‖ 0x05 ‖ ikB ‖ 0x05 ‖ ephAPk ‖ pqRatchetMsg` | `firstMsgAD` |
| 5-step first-message key schedule | `(rk, ck) → rootCreateChain(rk, DH(eph_A, SPK_B)) → chainKdfSeed(ck1_0) → deriveMsgKeys(mkSeed, spqrSalt?) → aes256CbcHmacEnc/Dec` | `Model.initiate` / `Model.accept`, `MessageKeys` (`Model.lean`) |
| Classical freshness (`-D DH`) | clean session whose `DH(EK_A, SPK_B)` leg (under honest XEdDSA signature), `DH(EK_A, IK_B)` leg, or `DH(EK_A, OPK_B)` leg has uncorrupted secrets; the session's peer must also have been honest and uncorrupted when it started (`fresh := honestPeer.isSome`, [DEV-PQ24](DEVIATIONS.md#dev-pq24)); there is no `PQSPK` disjunct ([DEV-PQ20](DEVIATIONS.md#dev-pq20)) | `keyIndInitCorruptionClause`, `isKeyIndInitStillFresh`, `isKeyIndRespStillFresh`, `authInitCorruptionClause`, `allTestedClean` (`Game.lean`) |
| KOSK registration | adversary-controlled identity and pre-key registration requires presenting the corresponding secret scalar | `registerKey`, `registerAdvKey`, `koskBundleOk`, `koskSenderOk` |
| FG24, BJKS24 | Fiedler–Günther, ePrint 2024/702; Bhargavan–Jacomme–Kiefer–Schmidt, USENIX Security 2024 | cited in [`DEVIATIONS.md`](DEVIATIONS.md) (DEV-PQ*) |
| SH-CR | BJKS24 Def. 1, semi-honest collision resistance of a KEM | `KemShCr` (`Assumptions.lean`) |
| `δ_corr` | FG24's KEM correctness error | none: `kem_corr` assumes `δ_corr = 0` ([DEV-PQ21](DEVIATIONS.md#dev-pq21)) |
| one-time vs last-resort `PQSPK_B` | libsignal and FG24 have both one-time and last-resort Kyber pre-keys | only last resort is modelled ([DEV-PQ22](DEVIATIONS.md#dev-pq22)) |

## 2. libsignal and protocol terms

| Term | Meaning |
|---|---|
| root key, chain key, message key | the three key levels of the Double Ratchet |
| ratchet key | a party's current X25519 key pair; its public half is in every header |
| eager ratchet step | libsignal's `dh_ratchet_step`: on receiving a new ratchet key, it draws the next sending key pair and runs both root-KDF steps at once (DEV-LS1) |
| window of `P` | from a receive that starts a new epoch of `P` until `P`'s next send (DEV-LS2) |
| receiver chain | state for one epoch of incoming messages; libsignal keeps at most 5 (`MAX_RECEIVER_CHAINS`) |
| `MAX_FORWARD_JUMPS` | 25,000: how far ahead a message may be (`maxForwardJumps`) |
| `MAX_MESSAGE_KEYS` | 2,000 skipped keys kept per chain |
| `previous_counter` (pn) | a header field: index of the previous sending chain minus 1; MACed, never read |
| signed pre-key (SPK) | Bob's medium-term key pair, published in his pre-key bundle; his initial ratchet key |
| `SignalMessage`, `PreKeySignalMessage` | libsignal's message types; the second wraps the first with handshake data |
| `SessionRecord` | libsignal's serialized session state |
| prost | the Rust protobuf library libsignal uses; `protoSignalCodec` is its Lean model |
| X3DH, PQXDH | the extended Diffie–Hellman handshake; Signal's hybrid X25519 + Kyber1024 successor, named "post-quantum extended Diffie–Hellman" (`SignalPqxdh`, `LibsignalBinary/Specifications/SignalPqxdh/Model.lean` and
`Computational/Specifications/Pqxdh/Game.lean`). The results here are classical only ([DEV-PQ19](DEVIATIONS.md#dev-pq19)) |
| SPQR | Sparse Post-Quantum Ratchet, libsignal's third ratchet; off in the verified image |
| HKDF, HMAC, MAC | HMAC-based key derivation; hash-based message authentication code; MAC |
| AES-256-CBC, PKCS#7 | the block cipher in cipher block chaining mode, and its padding |
| X25519 | the Curve25519 Diffie–Hellman function |
| Kyber1024 | the key encapsulation mechanism (KEM) in PQXDH: round-3 Kyber1024, not FIPS 203 ML-KEM-1024 ([DEV-PQ2](DEVIATIONS.md#dev-pq2)); `1568`-byte public key, `1568`-byte ciphertext, `32`-byte shared secret. In the results it enters only through `KemShCr` (BJKS24 SH-CR), a public-key collision term, and `KemDeltaCorrect P δ_kem` ([DEV-PQ21](DEVIATIONS.md#dev-pq21)) |
| XEdDSA | Signal's signature scheme using a Curve25519 key pair to sign and verify Edwards25519 signatures over `SPK_B` and `PQSPK_B` (`xeddsaVerifyRef` in `Model.lean`) |
| HNDL (harvest-now-decrypt-later) | name of the game variants `pqxdhHndlKeyIndExp`, `pqxdhHndlFirstMsgExp` (`Computational/Proofs/SpecLemmas/SignalPqxdh/Game.lean`): a classical adversary given every honest X25519 secret by `revealDhSecrets`, with the random oracle disabled. Defined only: **no HNDL or post-quantum security is claimed**, and their bounds are not part of any result ([DEV-PQ19](DEVIATIONS.md#dev-pq19)) |

## 3. Lean, VCVio and Mathlib notation

| Notation | Meaning |
|---|---|
| `OracleComp`, `ProbComp` | VCVio's computations with oracle access; without oracles |
| `$ᵗ T` | sample uniformly from the type `T` |
| `𝒟[c]`, `Pr[...]` | the output distribution of `c`; a probability |
| `boolBias` | `2·|Pr[1] − 1/2|`, the advantage of a hidden-bit game |
| `ℝ≥0∞` | extended non-negative reals, where bounds live |
| `simulateQ`, `StateT` | run a computation against oracle implementations; state monad |
| `Finset.range n` | `{0, …, n − 1}` |
| `#print axioms` | lists the axioms a theorem depends on |
| std3 | `propext`, `Classical.choice`, `Quot.sound` |
| `sorryAx` | the axiom behind `sorry`; absent from every headline |
| `bv_decide` certificate | an axiom stating that a Lean-verified LRAT checker accepted a SAT certificate |
| `rfl` | proof by definitional equality |

## 4. Names in the statement

| Name | Meaning |
|---|---|
| T | the statement files, `defaultStatementFiles` in `scripts/TrustedClosure.lean` (30 files): exactly the files that define what the theorems of `Computational/Theorems/` say; Tier 1 of the trusted base, read in full (`Computational/docs/TRUSTED_BASE.md` §1, §2) |
| theorem file | a file of `Computational/Theorems/`: it states the main theorems, each `NAME := NAME_proof` with the proof in `Computational/Proofs/`; Tier 1 of the trusted base, like T |
| `libsignalSessionScheme` | the Lean model of libsignal's session as an SM scheme ("the session model") |
| `lFig8` | ACD19 Fig. 8 instantiated with libsignal's primitives |
| `Refine.sim` | the reduction from the session model to `lFig8` (`LibsignalSim.simRun … none`; it and the window variant `Refine.simWin k` are in `Computational/Proofs/SpecLemmas/Session/ACD19/Ratchet/LibsignalSimShallow.lean`, and `Refine.simWin k` has its query bounds in `Computational/Proofs/CryptoGames/Ratchet/LibsignalSessionStatements.lean`) |
| `binStateOf` | maps a session-model state to the binary's state (the serialized record) |
| `shortCiphertext` | the injection filter: shorter than 2^32 bytes |
| `spqrOffSessionParams`, `EnvChoice`, `hookTableE`, `runE` | the session model's parameters at the free primitives `C : Crypto`; machine environment; hook table; one call on the machine |
| `fsShortBound`, `fsCompBound`, `fig8ShortBound`, `multiSlotAdv` | ACD19 Thm 5's and Thm 6's bounds for libsignal (`fsShortBound`, `fsCompBound` and `fig8ShortBound` in `Computational/Proofs/SpecLemmas/Session/ACD19/Ratchet/LibsignalBound.lean`, `multiSlotAdv` in `Computational/Specifications/Session/ACD19/Ratchet/LibsignalBound.lean`: `fsShortBound = fsCompBound + 4 * macForgeryTerm C qd`, summing `chainPRGTerm`, `2 * saltPRFTerm`, `wireOtccaTerm` over `fsSlotCount qR = 2·qR + 25001` active slots via the multi-cell reduction `multiSlotAdv`, plus one global per-chain MAC-forgery hop `4 * macForgeryTerm C qd` outside the slot sum; imported directly by `Statement.lean`; generic Thm 6 counterpart `SM.Construction.theorem6Bound` in `Computational/Proofs/CryptoGames/SM/Theorem6.lean`) |
| `macForgeryProb`, `forgedEpochStartSpuriousStepTerm`, `spuriousStepTerm`, `epoch0Term`, `epoch0Distinguisher`, `δ` | the 8-byte MAC-tag term, the window unknown-chain spurious-step term (DEV-LS12), the evicted-epoch spurious-step term (DEV-LS11), the epoch-0 term and its PRG distinguisher (DEV-LS26), the key-collision probability (DEV-LS18) |
| `ratchetKeyAdmissible`, `configR1OnCurve` | the on-curve injection filter (DEV-LS5); the restricted game with it |
| `LibsignalMsgPublicPart` | the public part of a message: `previous_counter`, SPQR fields, addresses |
| `Dh`, `encT`, `decT`, `encPt` | the abstract DH group and its encodings |
| `progP`, `hookTableP` / `hooksP`, `outcomeP`, `DemandBoundedP` | the machine, extended hook table (`PqxdhHooks.lean`), single-call outcome, and heap hypothesis (`PqxdhStatement.lean`) for the four PQXDH binary entries (`session_initiate`, `session_recv_prekey`, `session_send_wire`, `session_recv_wire`) |
| `modelPrims`, `encodeRecordUnderExtras` | the bridge from `C : Crypto` and `Q : PqxdhPrims` to `SignalPqxdh.Primitives` (`PqxdhModelLink.lean`); the generalized `SessionRecord` encoder carrying public PQXDH handshake metadata (`StateX.lean`) |
| `LibsignalPqxdhCorrectStmt`, `LibsignalPqxdhRejectStmt`, `LibsignalPqxdhSessionStmt` | the binary handshake correctness with SPQR V1, invalid-signature/tag rejection, and wire-entry session refinement statements for the PQXDH entries; no Lean declaration or theorem has these names. The CLI handshake correctness statement is Lemma 4, `libsignal_cli_pq_binary_correct_placed` (`Computational/Theorems/Main.lean`) |
| `SignalPqxdh.Security.PqxdhCorrectAndSecureδ`, `PqxdhSecureδ`, `PqxdhKeyIndSecureδ`, `PqxdhAuth1KeySecureδ` | the model-level PQXDH correctness, one-key random-oracle key-indistinguishability, and one-key first-message `Auth` statements under a `δ_kem`-correct KEM (`Computational/Specifications/Pqxdh/Security/HeadlineDelta.lean`, `Computational/Specifications/Pqxdh/Security/Auth/Headline.lean`), stated by the theorem `headlineδ` (`Computational/Theorems/Lemmas.lean`); standalone two-key `KeyInd` and `Auth`/`FirstMsg` statements (`Pqxdh2KeyKeyIndSecureδ`, `PqxdhAuthSecureδ`, `Pqxdh2KeySecureδ`, `Pqxdh2KeyCorrectAndSecureδ`) live in `Computational/Proofs/SignalPqxdh/TwoKeyAndAuthStatements.lean` outside the trusted base ([DEV-PQ13](DEVIATIONS.md#dev-pq13), [DEV-C5](DEVIATIONS.md#dev-c5)) |
| `GapDhWithSign`, `GapSigEufCma`, `KeyIndRoGap` | the joint one-key X25519 + XEdDSA assumptions (`GapDhWithSign`: single-pair X25519 Gap-DH modulo `pow8` with an XEdDSA signing oracle on the first challenge key; `GapSigEufCma`: XEdDSA EUF-CMA with the X25519 decisional DH oracle; `Assumptions.lean`, [DEV-PQ13](DEVIATIONS.md#dev-pq13)), and the random-oracle step `KeyIndRoGap` on the one-key game (`KeyInd1KeyRo.lean`, [DEV-CLI16](DEVIATIONS.md#dev-cli16)) |
| `KeyIndCostedReductionFamily`, `KeyIndCostedReductionBounds`, `KeyIndReductionQueryBounds` | the costed `ReductionDsl` reduction family and syntactic/semantic step, size, and query bounds for the one-key PQXDH `KeyInd` game (`Computational/Specifications/Pqxdh/Security/Headline.lean`); standalone two-key and `Auth` counterparts (`KeyInd2KeyCostedReductionFamily`, `AuthCostedReductionFamily`) live in `Computational/Proofs/SignalPqxdh/TwoKeyAndAuthStatements.lean` |
| `pqxdhKeyIndBound`, `deploymentSetup` | the concrete PQXDH `KeyInd` security bound (`Computational/Specifications/Pqxdh/Bound.lean`) and default multi-user scale parameters (`Computational/Proofs/SpecLemmas/Pqxdh/Security/BoundProofDefs.lean`; `pqxdhAuthBound` for `Auth` is in `Computational/Specifications/Pqxdh/Security/Auth/Game.lean`) |
| `PrfHmac`, `prfHmacExp`, `PrfHmacAdv` | real-or-random PRF security of HMAC-SHA256 under a uniform 32-byte key, the first-message MAC key; charged for Term 10 of `pqxdhAuthBound` in the standalone two-key `Auth` proof (`Computational/Proofs/SpecLemmas/SignalPqxdh/Assumptions.lean`, DEV-PQ31) |
| `AeadMuIntCtxt`, `aeadMuIntCtxtExp` | multi-key INT-CTXT of the first-message AEAD: one encryption per independent 80-byte `MessageKeys`, forgery attempts on any key; the intermediate game between the standalone `Auth` game (`aeadMuIntReductionAuth`) and `PrfHmac` (`Computational/Proofs/SpecLemmas/SignalPqxdh/Assumptions.lean`) |
| `prfHmacOfMu`, `prfHmacReductionAuth` | the transformer from an `AeadMuIntCtxtAdv` to a `PrfHmacAdv` (hybrid over key ranks, deferred forgery checks), and its application `prfHmacOfMu (aeadMuIntReductionAuth S b A)` in the standalone `Auth` proof (`Computational/Proofs/SignalPqxdh/Security/ReductionsAuthHmac.lean`; proof `aeadMuIntCtxt_le_prfHmac` in `Computational/Proofs/SignalPqxdh/Security/AuthPrfHmac.lean`) |
| `pow8_base_len` | the `CryptoWellFormedPrimitivesδ` law `P.pow8 p = P.pow8 (P.x25519Base e) → p.length = 32`: only a 32-byte key projects onto a base-point output; true for real X25519 (`KemCorrect.lean`, DEV-PQ31) |
| `SessionSecureUIds`, `SessionSecureSpkIds`, `LibsignalBinarySecureU`, `LibsignalBinarySecureSpk`, `spkLeakRed`, `hop2PrgRedK`, `hop2PrfRedK` | the uniform-start and leaked-signed-pre-key Double Ratchet statements and reductions (`SpkHop2Red.lean`, `SpkLeakRed.lean`, `StatementIds.lean`, `StatementIdsModel.lean`); no theorem of `Computational/Theorems/` states them |
| `ComposedSecurePrefixMixV1` | the model-level PQXDH + Double Ratchet + SPQR V1 composition (`Computational/Proofs/SpecLemmas/Session/StatementComposed.lean`), proved conditionally on `HiddenSaltBoundV1HoldsEx`; unpartnered first-message payload privacy and authentication are covered by Lemma 1's one-key `Auth` conjunct, not by this composition ([DEV-C5](DEVIATIONS.md#dev-c5)) |

## 5. Former project names

Older docstrings, commits and pull requests use these names. The documentation does not.

| Former name | Now |
|---|---|
| rung 7a, 7a | the session model (`libsignalSessionScheme`, `CryptoGames.LibsignalSM`), its proof directory (`Computational/Proofs/CryptoGames/Ratchet/SessionProofs/`), and its theorem `CryptoVerification.LibsignalSession.libsignal_session_sm_r1_proto` |
| rung 7b, stage 1 / 2 / 3 | the binary refinement of the session (stages: base hooks; session program and its hooks; store-level API proofs) |
| rung 6 | the X25519 ratchet as a CKA and the root KDF as a PRF-PRNG |
| rung 5, 5w | ACD19 Thm 5 for libsignal's symmetric ratchet (on the wire) |
| rung 4, rung 3c, rungs 0–3 | message-key KDF; the wire AEAD; AES-CBC, CBC decryption, HMAC, the per-message AEAD |
| R1 game | the headline's restricted game (DEV-LS1–LS6) |
| variant M | an earlier version of the binary statement (pull request #186) |
| W0, W3, MessageDecrypt, MessageEncrypt, W45 | the session-API model; its unproved API statements; the decrypt proof; the encrypt proof; the store-call proofs |
| T-a, T-b, T-c, T-d, T-e, T-f, T-g, T-q, suffix `s` | proof steps of the session-model theorem in `Computational/Proofs/CryptoGames/Ratchet/SessionProofs/`: pub-to-AD reduction; Thm 5 for the instance; equal-pub and one-epoch reductions; salt hop and wire hop; refinement (`Refinement/`); correctness (`Correctness/`); OT-CCA restrictions and query bounds; "at prost's codec" (`ProstCodec/`) |
| `Short` (`SessionProofs/Short/`) | at prost's codec, fields shorter than 2^63 bytes (`Computational/Proofs/CryptoGames/Ratchet/SessionProofs/ProstCodec/`) |
| gap G1, G3, G5 | DEV-LS1 / DEV-CKA11; DEV-LS5; DEV-LS13 |
| plan §4e.9 H2, H3, H3', H4, H5 | DEV-LS8, LS3, LS4, LS27, LS26 (not ACD19's hybrids) |
| option (h) | the public message part `LibsignalMsgPublicPart` (DEV-LS13) |
| review L1, L3, L4 | spurious step (DEV-LS11), epoch-0 term (DEV-LS26), off-curve keys (DEV-LS5) |
| "decision X" (D2, D5, F1(a), F3–F6, A1, R2-6, R3-1, 21, …) | design decisions recorded in old commit messages; each is now stated by its content |
| "deviation n of file F" | the `DEV-*` IDs ([`DEVIATIONS.md`](DEVIATIONS.md), "Former names") |
| `φE`, `keepE` | `binStateOf`, `shortCiphertext` |
| `Phi.lean`, `Spec.lean` (T) | `State.lean`, `Machine.lean` |

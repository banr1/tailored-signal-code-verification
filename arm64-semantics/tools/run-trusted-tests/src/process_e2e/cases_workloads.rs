// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Differential test cases for the 14 workload guest binaries (`base64_codec` through
//! `collatz_stats`): real CLI-style programs over `stdin`, `argv`, `environ`, and `cwd` files that
//! use only modeled syscalls and must match `qemu-aarch64` exactly (`[TEST ONLY]`).

use std::path::Path;

use anyhow::Result;

use super::cases::{exited_match, file_bytes, run_and_record};
use super::types::{CaseCategory, FileEntry, VectorCase};

/// One `CaseCategory::Match` workload case (fast runner only, no pre-created directories).
struct Workload<'a> {
    id: &'a str,
    program: &'a str,
    args: Vec<&'a str>,
    envp: Vec<&'a str>,
    stdin: Vec<u8>,
    files: Vec<FileEntry>,
    watched: Vec<&'a str>,
    code: u64,
    notes: &'a str,
}

impl<'a> Workload<'a> {
    fn new(id: &'a str, args: Vec<&'a str>, stdin: &[u8], code: u64, notes: &'a str) -> Self {
        let program = id.split('/').next().unwrap_or(id);
        Self {
            id,
            program,
            args,
            envp: vec![],
            stdin: stdin.to_vec(),
            files: vec![],
            watched: vec![],
            code,
            notes,
        }
    }

    fn envp(mut self, envp: Vec<&'a str>) -> Self {
        self.envp = envp;
        self
    }

    fn files(mut self, files: Vec<FileEntry>, watched: Vec<&'a str>) -> Self {
        self.files = files;
        self.watched = watched;
        self
    }
}

fn pattern(len: usize, mul: usize, add: usize) -> Vec<u8> {
    (0..len).map(|i| ((i * mul + add) & 0xff) as u8).collect()
}

fn base64_of(data: &[u8]) -> Vec<u8> {
    const A: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut raw = Vec::new();
    for c in data.chunks(3) {
        let n = (c[0] as u32) << 16
            | (*c.get(1).unwrap_or(&0) as u32) << 8
            | *c.get(2).unwrap_or(&0) as u32;
        raw.push(A[(n >> 18) as usize & 63]);
        raw.push(A[(n >> 12) as usize & 63]);
        raw.push(if c.len() > 1 {
            A[(n >> 6) as usize & 63]
        } else {
            b'='
        });
        raw.push(if c.len() > 2 {
            A[n as usize & 63]
        } else {
            b'='
        });
    }
    let mut out = Vec::new();
    for line in raw.chunks(60) {
        out.extend_from_slice(line);
        out.extend_from_slice(b"\r\n");
    }
    out
}

fn workloads() -> Vec<Workload<'static>> {
    let lorem: &[u8] = b"The quick brown fox jumps over the lazy dog; pack my box with five dozen liquor jugs! 0123456789\n";
    let all_bytes: Vec<u8> = (0u8..=255).collect();

    let mut squeeze = vec![b'A'; 16];
    squeeze.extend(std::iter::repeat_n(0u8, 80));
    squeeze.extend_from_slice(b"tail bytes\x01\x02\x7f");

    let mut rle_in: Vec<u8> = b"aaaabbbcccccccccccd\n".to_vec();
    rle_in.extend(std::iter::repeat_n(b'z', 300));
    rle_in.extend_from_slice(b"xyz");
    let mut rle_rt = Vec::new();
    for i in 0..4096usize {
        rle_rt.push(b"abcd"[(i / 37) % 4]);
    }

    let words: &[u8] =
        b"pear\napple\nfig\napple\nkiwi\npear\napple\nbanana\nfig\ncherry\napple\nkiwi";

    let log: &[u8] = b"INFO boot ok\nWARN disk 91% full\nerror: link down\nINFO retry\nERROR: link down again\ninfo done\n";

    let mut file_a = b"alpha line 1\nalpha line 2\n".to_vec();
    file_a.extend_from_slice(&pattern(40, 7, 3));

    vec![
        // base64_codec
        Workload::new(
            "base64_codec/enc_wrap",
            vec!["base64_codec", "enc"],
            lorem,
            0,
            "Encodes 97 bytes into 132 base64 symbols wrapped at 76 columns (`=` padding on the final quantum).",
        ),
        Workload::new(
            "base64_codec/dec_all_bytes",
            vec!["base64_codec", "dec"],
            &base64_of(&all_bytes),
            0,
            "Decodes CRLF-wrapped base64 of all 256 byte values back to raw binary `stdout`.",
        ),
        Workload::new(
            "base64_codec/dec_invalid",
            vec!["base64_codec", "dec"],
            b"SGVsbG8s\nIHdv*cmxk\n",
            1,
            "Rejects `*` with its byte offset on `stderr` and writes nothing to `stdout` (`exit 1`).",
        ),
        Workload::new(
            "base64_codec/usage",
            vec!["base64_codec"],
            b"",
            2,
            "Missing mode prints usage on `stderr` without reading `stdin` (`exit 2`).",
        ),
        // hexdump
        Workload::new(
            "hexdump/text",
            vec!["hexdump"],
            b"Hello, hexdump!\nsecond line\twith tab\n",
            0,
            "Canonical `hexdump -C` rows for printable text with a partial final row and length trailer.",
        ),
        Workload::new(
            "hexdump/squeeze",
            vec!["hexdump"],
            &squeeze,
            0,
            "Collapses 4 identical all-zero rows into one `*` line, then dumps a short non-printable tail.",
        ),
        Workload::new(
            "hexdump/all_bytes_verbose",
            vec!["hexdump", "-v"],
            &all_bytes,
            0,
            "`-v` dumps all 256 byte values (16 rows) with `.` for non-printable gutter bytes.",
        ),
        Workload::new(
            "hexdump/bad_option",
            vec!["hexdump", "-x"],
            b"ignored",
            2,
            "Unknown option is echoed on `stderr` (`exit 2`).",
        ),
        // sha256sum
        Workload::new(
            "sha256sum/abc",
            vec!["sha256sum"],
            b"abc",
            0,
            "FIPS 180-4 test vector `SHA-256(\"abc\")` = `ba7816bf...f20015ad`.",
        ),
        Workload::new(
            "sha256sum/multiblock_1000",
            vec!["sha256sum"],
            &pattern(1000, 31, 7),
            0,
            "1000-byte binary input spanning 16 compression blocks (two-block padding tail not needed).",
        ),
        Workload::new(
            "sha256sum/check_ok",
            vec![
                "sha256sum",
                "-c",
                "BA7816BF8F01CFEA414140DE5DAE2223B00361A396177A9CB410FF61F20015AD",
            ],
            b"abc",
            0,
            "`-c` accepts an upper-case expected digest after case folding (`-: OK`).",
        ),
        Workload::new(
            "sha256sum/check_fail",
            vec![
                "sha256sum",
                "-c",
                "0000000000000000000000000000000000000000000000000000000000000000",
            ],
            b"abc",
            1,
            "`-c` mismatch prints `FAILED` with the actual digest on `stdout` (`exit 1`).",
        ),
        // rle_codec
        Workload::new(
            "rle_codec/compress",
            vec!["rle_codec", "c"],
            &rle_in,
            0,
            "Compresses mixed short runs and a 300-byte run (split at the 255 cap) into binary pairs.",
        ),
        Workload::new(
            "rle_codec/decompress",
            vec!["rle_codec", "d"],
            &[3, b'a', 1, b'\n', 255, b'-', 2, 0x00, 1, b'\n'],
            0,
            "Expands 5 pairs including a 255-byte run and NUL bytes.",
        ),
        Workload::new(
            "rle_codec/corrupt",
            vec!["rle_codec", "d"],
            &[3, b'a', 0, b'b', 2, b'c'],
            1,
            "Zero run count in pair 1 is reported on `stderr` before any output (`exit 1`).",
        ),
        Workload::new(
            "rle_codec/roundtrip_4k",
            vec!["rle_codec", "rt"],
            &rle_rt,
            0,
            "Compress + decompress + compare a 4 KiB input of 37-byte runs in memory, printing stats.",
        ),
        // sort_uniq
        Workload::new(
            "sort_uniq/default",
            vec!["sort_uniq"],
            words,
            0,
            "Bytewise sort + `uniq -c` of 12 lines without a trailing newline.",
        ),
        Workload::new(
            "sort_uniq/by_count",
            vec!["sort_uniq", "-n"],
            words,
            0,
            "`-n` orders groups by descending count with bytewise tie-breaking.",
        ),
        Workload::new(
            "sort_uniq/reverse_dups",
            vec!["sort_uniq", "-r", "-d"],
            words,
            0,
            "`-r -d` prints only duplicated lines in reverse bytewise order.",
        ),
        // grep_lite
        Workload::new(
            "grep_lite/numbered",
            vec!["grep_lite", "-n", "link"],
            log,
            0,
            "Case-sensitive substring match with `lineno:` prefixes.",
        ),
        Workload::new(
            "grep_lite/icase_count",
            vec!["grep_lite", "-i", "-c", "error"],
            log,
            0,
            "`-i -c` counts ASCII case-insensitive matches only.",
        ),
        Workload::new(
            "grep_lite/invert",
            vec!["grep_lite", "-v", "INFO"],
            log,
            0,
            "`-v` prints the lines that do not contain the pattern.",
        ),
        Workload::new(
            "grep_lite/no_match",
            vec!["grep_lite", "panic"],
            log,
            1,
            "No selected line: empty `stdout` and POSIX `grep` status `1`.",
        ),
        Workload::new(
            "grep_lite/usage",
            vec!["grep_lite", "-n"],
            log,
            2,
            "Missing pattern prints usage on `stderr` (`exit 2`).",
        ),
        // rpn_calc
        Workload::new(
            "rpn_calc/ok",
            vec!["rpn_calc"],
            b"3 4 + 2 *\n\n10 3 % 7 neg swap -\n1 2 3 4 5 sum dup *\n-9223372036854775807 1 -\n100 7 /\n",
            0,
            "Evaluates 5 expressions (blank line skipped) covering `+ * % neg swap sum dup /` and `i64::MIN`.",
        ),
        Workload::new(
            "rpn_calc/div_zero",
            vec!["rpn_calc"],
            b"6 7 *\n1 0 /\n2 2 +\n",
            1,
            "Flushes line 1's result, then reports division by zero on line 2 and stops (`exit 1`).",
        ),
        Workload::new(
            "rpn_calc/errors",
            vec!["rpn_calc"],
            b"9223372036854775807 1 +\n",
            1,
            "Checked `i64` addition overflow is reported on `stderr` with no `stdout` (`exit 1`).",
        ),
        // file_copy
        Workload::new(
            "file_copy/cp",
            vec!["file_copy", "cp", "src.bin", "dst.bin"],
            b"",
            0,
            "Stock `fs::read` + `fs::write` (`O_CREAT|O_TRUNC`) + `File::open` read-back of a 1 KiB binary file.",
        )
        .files(vec![file_bytes("src.bin", &pattern(1024, 13, 5))], vec!["src.bin", "dst.bin"]),
        Workload::new(
            "file_copy/upper_overwrite",
            vec!["file_copy", "upper", "notes.txt", "out.txt"],
            b"",
            0,
            "Uppercases into an existing longer `out.txt`, which `O_TRUNC` must shrink.",
        )
        .files(
            vec![
                file_bytes("notes.txt", b"hello, World! mixed Case 123\n"),
                file_bytes("out.txt", &[b'#'; 200]),
            ],
            vec!["notes.txt", "out.txt"],
        ),
        Workload::new(
            "file_copy/cat_missing",
            vec!["file_copy", "cat", "a.txt", "missing.txt", "b.txt"],
            b"",
            1,
            "Concatenates `a.txt` and `b.txt` with headers; `missing.txt` reports `ENOENT` on `stderr` (`exit 1`).",
        )
        .files(
            vec![file_bytes("a.txt", &file_a), file_bytes("b.txt", b"bravo\n")],
            vec![],
        ),
        // json_lint
        Workload::new(
            "json_lint/valid",
            vec!["json_lint"],
            br#"{"name": "widget", "tags": ["a", "b\n\u00e9"], "n": -12.5e+3, "ok": true,
 "nested": {"x": [1, 2, [3, {"y": null}]], "z": false}, "empty": [], "e2": {}}"#,
            0,
            "Counts objects, arrays, strings, numbers, and literals of a nested document (max depth 5).",
        ),
        Workload::new(
            "json_lint/mismatched",
            vec!["json_lint"],
            b"{\"a\": [1, 2}, \"b\": 3}",
            1,
            "`}` closing a `[` is reported with both offsets on `stderr` (`exit 1`).",
        ),
        Workload::new(
            "json_lint/bad_escape",
            vec!["json_lint"],
            b"[\"ok\", \"bad \\x escape\"]",
            1,
            "Invalid `\\x` string escape is reported with its offset (`exit 1`).",
        ),
        // bignum
        Workload::new(
            "bignum/fact_100",
            vec!["bignum", "fact", "100"],
            b"",
            0,
            "`100!` (158 digits) via repeated base-`10^9` small multiplication.",
        ),
        Workload::new(
            "bignum/fib_500",
            vec!["bignum", "fib", "500"],
            b"",
            0,
            "`F(500)` (105 digits) via 500 limb-wise big additions.",
        ),
        Workload::new(
            "bignum/pow2_1000",
            vec!["bignum", "pow2", "1000"],
            b"",
            0,
            "`2^1000` (302 digits) via 1000 doublings.",
        ),
        Workload::new(
            "bignum/out_of_range",
            vec!["bignum", "fact", "5000"],
            b"",
            2,
            "`N > 2000` is rejected on `stderr` (`exit 2`).",
        ),
        // matrix_mul
        Workload::new(
            "matrix_mul/default_8",
            vec!["matrix_mul"],
            b"",
            0,
            "Default `8 x 8`, seed `1`: trace, checksum, first row, and identity self-check.",
        ),
        Workload::new(
            "matrix_mul/n24_seed7",
            vec!["matrix_mul", "24", "7"],
            b"",
            0,
            "`24 x 24` (two 13.8k-MAC products) with seed `7`.",
        ),
        Workload::new(
            "matrix_mul/bad_n",
            vec!["matrix_mul", "0"],
            b"",
            2,
            "`N = 0` is rejected with usage on `stderr` (`exit 2`).",
        ),
        // env_lookup
        Workload::new(
            "env_lookup/found",
            vec!["env_lookup", "HOME", "LANG", "EMPTY"],
            b"",
            0,
            "musl `getenv` finds three variables, including an empty value.",
        )
        .envp(vec!["PATH=/bin", "HOME=/home/widget", "EMPTY=", "LANG=C.UTF-8"]),
        Workload::new(
            "env_lookup/missing",
            vec!["env_lookup", "HOME", "NOPE", "HOMEX"],
            b"",
            1,
            "Unset names (including a prefix-extended `HOMEX`) are reported on `stderr` (`exit 1`).",
        )
        .envp(vec!["HOME=/root", "HOMEDIR=/x"]),
        Workload::new(
            "env_lookup/sorted",
            vec!["env_lookup", "--sorted"],
            b"",
            0,
            "Sorts and prints all 5 raw `environ` entries plus a count.",
        )
        .envp(vec!["ZETA=26", "alpha=1", "MID=m", "A=first", "B=2=two"]),
        // rot_cipher
        Workload::new(
            "rot_cipher/rot13",
            vec!["rot_cipher", "rot13"],
            b"Hello, World! Uryyb? \xc3\xa9 123\n",
            0,
            "ROT13 over ASCII letters; punctuation, digits, and UTF-8 bytes pass through.",
        ),
        Workload::new(
            "rot_cipher/caesar_neg",
            vec!["rot_cipher", "caesar", "-29"],
            b"Attack at Dawn, ZEBRA zebra.\n",
            0,
            "Signed shift `-29` reduces to `+23` via `rem_euclid(26)`.",
        ),
        Workload::new(
            "rot_cipher/freq",
            vec!["rot_cipher", "freq"],
            lorem,
            0,
            "Case-folded letter histogram (two 13-column rows) plus the most frequent letter.",
        ),
        Workload::new(
            "rot_cipher/bad_shift",
            vec!["rot_cipher", "caesar", "three"],
            b"abc",
            2,
            "Non-numeric shift is rejected on `stderr` (`exit 2`).",
        ),
        // collatz_stats
        Workload::new(
            "collatz_stats/range_1_1000",
            vec!["collatz_stats", "1", "1000"],
            b"",
            0,
            "Chain statistics for `1..=1000` (longest `871:178`, peak `703:250504`) and histogram.",
        ),
        Workload::new(
            "collatz_stats/single_27",
            vec!["collatz_stats", "27", "27"],
            b"",
            0,
            "The classic `27` chain: 111 steps peaking at 9232.",
        ),
        Workload::new(
            "collatz_stats/bad_range",
            vec!["collatz_stats", "10", "5"],
            b"",
            2,
            "`LO > HI` is rejected on `stderr` (`exit 2`).",
        ),
    ]
}

/// Run all workload cases under `qemu-aarch64` and append them to `cases`.
pub(super) fn record_workload_cases(
    cases: &mut Vec<VectorCase>,
    repo_root: &Path,
    qemu_bin: &Path,
) -> Result<()> {
    for w in workloads() {
        run_and_record(
            cases,
            repo_root,
            qemu_bin,
            w.id,
            w.program,
            CaseCategory::Match,
            w.args,
            w.envp,
            &w.stdin,
            vec![],
            w.files,
            w.watched,
            false,
            false,
            false,
            exited_match(w.code, w.notes),
        )?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::process_e2e::build::GUEST_BINARIES;

    #[test]
    fn every_workload_names_a_guest_binary() {
        for w in workloads() {
            assert!(
                GUEST_BINARIES.iter().any(|b| b.name == w.program),
                "{} has no GuestBinarySpec",
                w.id
            );
        }
    }

    #[test]
    fn every_workload_binary_has_two_or_more_cases() {
        let ws = workloads();
        for name in ws.iter().map(|w| w.program) {
            assert!(
                ws.iter().filter(|w| w.program == name).count() >= 2,
                "{name}"
            );
        }
    }
}

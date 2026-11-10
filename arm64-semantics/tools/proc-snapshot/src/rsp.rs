// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Minimal GDB Remote Serial Protocol client for `proc-snapshot` (`[CASE-STUDIES TCB]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[CASE-STUDIES TCB]` — every byte and register value in a process snapshot
//!   passes through this file (trusted only by snapshot-based proofs, outside the core engine
//!   `[tcb]`). Keep it small: only the packets `proc-snapshot` needs.
//! - **Purpose:** Talks to qemu-user's gdbstub over TCP in acknowledged mode: packet framing
//!   (`$<payload>#<checksum>`, `}` escapes, `*` run-length decoding), `qSupported`, `?`,
//!   `qXfer:features:read` (target description and its `xi:include`d files), `p<n>`,
//!   chunked `m addr,len`, `Z0`, `c`, stop replies (`T`/`S`), and `k`.
//!
//! # Key Types & Functions
//! - [`Rsp`]: connected client. [`frame`] / [`decode_body`]: wire encoding helpers.
//! - [`parse_stop`]: stop-reply signal. [`parse_target_regs`]: `<reg>` list from target XML.
//!
//! # When to Read This File
//! - Read this file when auditing how snapshot bytes and registers are obtained.

use anyhow::{Context, Result, bail, ensure};
use std::io::{Read, Write};
use std::net::TcpStream;

/// Frames `payload` as `$payload#cs`, escaping `#$}*`.
pub fn frame(payload: &[u8]) -> Vec<u8> {
    let mut body = Vec::with_capacity(payload.len() + 4);
    for &b in payload {
        if matches!(b, b'#' | b'$' | b'}' | b'*') {
            body.extend_from_slice(&[b'}', b ^ 0x20]);
        } else {
            body.push(b);
        }
    }
    let cs = body.iter().fold(0u8, |a, &b| a.wrapping_add(b));
    let mut out = vec![b'$'];
    out.extend_from_slice(&body);
    out.extend_from_slice(format!("#{cs:02x}").as_bytes());
    out
}

/// Decodes a received packet body (between `$` and `#`): run-length expansion, then `}` escapes.
pub fn decode_body(raw: &[u8]) -> Result<Vec<u8>> {
    let mut out: Vec<u8> = Vec::with_capacity(raw.len());
    let mut i = 0;
    while i < raw.len() {
        match raw[i] {
            b'}' => {
                let b = *raw.get(i + 1).context("rsp: dangling '}' escape")?;
                out.push(b ^ 0x20);
                i += 2;
            }
            b'*' => {
                let n = *raw.get(i + 1).context("rsp: dangling '*' run length")?;
                ensure!(n >= 29, "rsp: bad run-length byte {n:#x}");
                let prev = *out
                    .last()
                    .context("rsp: run length without a previous byte")?;
                out.extend(std::iter::repeat_n(prev, usize::from(n - 29)));
                i += 2;
            }
            b => {
                out.push(b);
                i += 1;
            }
        }
    }
    Ok(out)
}

/// Decodes a hex string into bytes.
pub fn hex_decode(s: &[u8]) -> Result<Vec<u8>> {
    ensure!(s.len().is_multiple_of(2), "rsp: odd-length hex reply");
    let nib = |c: u8| -> Result<u8> {
        Ok(match c {
            b'0'..=b'9' => c - b'0',
            b'a'..=b'f' => c - b'a' + 10,
            b'A'..=b'F' => c - b'A' + 10,
            _ => bail!("rsp: non-hex byte {c:#x} in reply"),
        })
    };
    s.chunks(2)
        .map(|p| Ok((nib(p[0])? << 4) | nib(p[1])?))
        .collect()
}

/// Returns the signal number of a `T<sig>...` / `S<sig>` stop reply.
pub fn parse_stop(reply: &[u8]) -> Result<u8> {
    match reply.first() {
        Some(b'T' | b'S') if reply.len() >= 3 => Ok(hex_decode(&reply[1..3])?[0]),
        _ => bail!(
            "rsp: expected a stop reply, got {:?}",
            String::from_utf8_lossy(reply)
        ),
    }
}

/// One `<reg>` entry of a target description.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TargetReg {
    pub name: String,
    pub bitsize: u32,
    pub regnum: u32,
}

fn xml_attr(tag: &str, key: &str) -> Option<String> {
    let pat = format!(" {key}=\"");
    let start = tag.find(&pat)? + pat.len();
    let len = tag[start..].find('"')?;
    Some(tag[start..start + len].to_string())
}

/// Lists `<xi:include href=...>` targets in document order.
pub fn parse_includes(xml: &str) -> Vec<String> {
    xml.split("<xi:include")
        .skip(1)
        .filter_map(|t| xml_attr(t, "href"))
        .collect()
}

/// Parses `<reg>` entries in document order; `regnum` defaults to previous + 1 (GDB rule).
pub fn parse_target_regs(xml: &str, next_regnum: &mut u32) -> Result<Vec<TargetReg>> {
    let mut regs = Vec::new();
    for t in xml.split("<reg ").skip(1) {
        let tag = format!(" {}", &t[..t.find('>').context("rsp: unterminated <reg>")?]);
        let name = xml_attr(&tag, "name").context("rsp: <reg> without name")?;
        let bitsize = xml_attr(&tag, "bitsize")
            .context("rsp: <reg> without bitsize")?
            .parse()?;
        let regnum = match xml_attr(&tag, "regnum") {
            Some(n) => n.parse()?,
            None => *next_regnum,
        };
        *next_regnum = regnum + 1;
        regs.push(TargetReg {
            name,
            bitsize,
            regnum,
        });
    }
    Ok(regs)
}

/// Connected RSP client (acknowledged mode).
pub struct Rsp {
    sock: TcpStream,
    /// Maximum payload size the stub accepts / sends (`PacketSize` from `qSupported`).
    pub packet_size: usize,
}

impl Rsp {
    pub fn new(sock: TcpStream) -> Result<Self> {
        sock.set_read_timeout(Some(std::time::Duration::from_secs(60)))?;
        sock.set_nodelay(true)?;
        Ok(Self {
            sock,
            packet_size: 4096,
        })
    }

    fn byte(&mut self) -> Result<u8> {
        let mut b = [0u8; 1];
        self.sock
            .read_exact(&mut b)
            .context("rsp: connection read failed")?;
        Ok(b[0])
    }

    /// Sends one packet and waits for the `+` ack (retransmits on `-`).
    pub fn send(&mut self, payload: &[u8]) -> Result<()> {
        let pkt = frame(payload);
        for _ in 0..5 {
            self.sock.write_all(&pkt)?;
            match self.byte()? {
                b'+' => return Ok(()),
                b'-' => continue,
                b => bail!("rsp: expected ack, got {b:#x}"),
            }
        }
        bail!("rsp: packet rejected 5 times")
    }

    /// Receives one packet (skipping stray bytes before `$`), verifies the checksum, acks it.
    pub fn recv(&mut self) -> Result<Vec<u8>> {
        loop {
            while self.byte()? != b'$' {}
            let mut raw = Vec::new();
            loop {
                match self.byte()? {
                    b'#' => break,
                    b => raw.push(b),
                }
            }
            let cs = hex_decode(&[self.byte()?, self.byte()?])?[0];
            if raw.iter().fold(0u8, |a, &b| a.wrapping_add(b)) == cs {
                self.sock.write_all(b"+")?;
                return decode_body(&raw);
            }
            self.sock.write_all(b"-")?;
        }
    }

    pub fn request(&mut self, payload: &str) -> Result<Vec<u8>> {
        self.send(payload.as_bytes())?;
        self.recv()
    }

    /// `qSupported`: records `PacketSize`.
    pub fn handshake(&mut self) -> Result<String> {
        let r = String::from_utf8(self.request("qSupported:xmlRegisters=aarch64")?)?;
        for f in r.split(';') {
            if let Some(v) = f.strip_prefix("PacketSize=") {
                self.packet_size = usize::from_str_radix(v, 16)?;
            }
        }
        Ok(r)
    }

    /// `?`: current stop signal.
    pub fn halt_reason(&mut self) -> Result<u8> {
        let r = self.request("?")?;
        parse_stop(&r)
    }

    /// `qXfer:features:read:<annex>` until the `l` (last) chunk.
    pub fn read_feature(&mut self, annex: &str) -> Result<String> {
        let mut out = Vec::new();
        loop {
            let len = self.packet_size.saturating_sub(16).max(64);
            let r = self.request(&format!(
                "qXfer:features:read:{annex}:{:x},{len:x}",
                out.len()
            ))?;
            match r.split_first() {
                Some((b'm', d)) => out.extend_from_slice(d),
                Some((b'l', d)) => {
                    out.extend_from_slice(d);
                    return Ok(String::from_utf8(out)?);
                }
                _ => bail!(
                    "rsp: qXfer {annex} failed: {:?}",
                    String::from_utf8_lossy(&r)
                ),
            }
        }
    }

    /// All registers from `target.xml` and its includes, in document order.
    pub fn target_regs(&mut self) -> Result<Vec<TargetReg>> {
        let mut next = 0;
        let top = self.read_feature("target.xml")?;
        let mut regs = parse_target_regs(&top, &mut next)?;
        for inc in parse_includes(&top) {
            regs.extend(parse_target_regs(&self.read_feature(&inc)?, &mut next)?);
        }
        Ok(regs)
    }

    /// `p<n>`: one register as a little-endian integer (≤ 64 bits).
    pub fn read_reg(&mut self, regnum: u32) -> Result<u64> {
        let r = self.request(&format!("p{regnum:x}"))?;
        let bytes = hex_decode(&r).with_context(|| format!("rsp: p{regnum:x} reply"))?;
        ensure!(
            !bytes.is_empty() && bytes.len() <= 8,
            "rsp: p{regnum:x}: {} bytes",
            bytes.len()
        );
        Ok(bytes
            .iter()
            .rev()
            .fold(0u64, |a, &b| (a << 8) | u64::from(b)))
    }

    /// `g`: the raw register block (cross-checked against `p<n>` by the caller).
    pub fn read_all_regs(&mut self) -> Result<Vec<u8>> {
        let r = self.request("g")?;
        ensure!(
            r.first() != Some(&b'E'),
            "rsp: g failed: {:?}",
            String::from_utf8_lossy(&r)
        );
        hex_decode(&r)
    }

    /// `m addr,len` in packet-sized chunks. `Ok(None)` if the stub reports an error (unmapped).
    pub fn read_mem(&mut self, addr: u64, len: usize) -> Result<Option<Vec<u8>>> {
        let chunk = (self.packet_size.saturating_sub(16) / 2).max(16);
        let mut out = Vec::with_capacity(len);
        while out.len() < len {
            let n = chunk.min(len - out.len());
            let r = self.request(&format!("m{:x},{n:x}", addr + out.len() as u64))?;
            if r.first() == Some(&b'E') || r.is_empty() {
                return Ok(None);
            }
            let bytes = hex_decode(&r)?;
            ensure!(
                !bytes.is_empty() && bytes.len() <= n,
                "rsp: m returned {} bytes",
                bytes.len()
            );
            out.extend_from_slice(&bytes);
        }
        Ok(Some(out))
    }

    /// `Z0,addr,4`: software breakpoint.
    pub fn set_breakpoint(&mut self, addr: u64) -> Result<()> {
        let r = self.request(&format!("Z0,{addr:x},4"))?;
        ensure!(
            r == b"OK",
            "rsp: Z0 failed: {:?}",
            String::from_utf8_lossy(&r)
        );
        Ok(())
    }

    /// `c`: continue and wait for the next stop; returns its signal.
    pub fn cont(&mut self) -> Result<u8> {
        self.send(b"c")?;
        loop {
            let r = self.recv()?;
            match r.first() {
                Some(b'O') if r != b"OK" => continue, // console output
                Some(b'W' | b'X') => bail!("rsp: target exited: {}", String::from_utf8_lossy(&r)),
                _ => return parse_stop(&r),
            }
        }
    }

    /// `k`: kill the target (no reply expected).
    pub fn kill(&mut self) -> Result<()> {
        self.sock.write_all(&frame(b"k"))?;
        Ok(())
    }
}

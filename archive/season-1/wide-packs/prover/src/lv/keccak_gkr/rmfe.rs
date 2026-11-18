// Vendored from leanVM 0b850750 `crates/keccak_gkr/src/rmfe.rs` (tools/vendor.py; edits: lv/PATCHES.md).
//! The reverse multiplication-friendly embedding the protocol packs thirty-two instances with.
//!
//! `embed` sends thirty-two bits to a binary polynomial of degree at most 52, and `project` sends a
//! product of two embeddings back to the bitwise AND of what they embed:
//!
//! ```text
//!     project(embed(a) * embed(b)) = a & b
//! ```
//!
//! The polynomial is glued by the Chinese remainder theorem from fourteen small fields, each
//! holding a few bits as the values of a low-degree polynomial at `0`, `1` and `infinity`, plus
//! one bit carried by the leading coefficient.
//!
//! lvm2 W32 (lead decision D1): the (32, 53 -> 105) RMFE of `LvmVCore.rmfeFactors` (14 places, DEEP-AND's order;
//! leanVM's 7 are a prefix). The construction is leanVM's (and Lean's `rmfeFactor`) unchanged, on `u128` since a
//! product has 105 coefficients; a single-bit place of degree above one projects by the parity (Lean's `atOne`).

/// Bits one embedding carries.
pub const PACK: usize = 32;
/// Variables indexing the instances of a pack.
pub const PACK_BITS: usize = 5;
/// Coefficients of an embedding.
pub const EMBED_BITS: usize = 53;
/// Coefficients of a product of two embeddings.
pub const PROD_BITS: usize = 2 * EMBED_BITS - 1;

/// The moduli, with the number of bits each one holds (`LvmVCore.rmfeFactors`).
const FACTORS: [(u128, usize); 14] = [
    (0b10, 1),
    (0b11, 1),
    (0b1011, 2),
    (0b1101, 2),
    (0b100101, 3),
    (0b101001, 3),
    (0b101111, 3),
    (0b110111, 3),
    (0b111011, 3),
    (0b111101, 3),
    (0b111, 1),
    (0b10011, 2),
    (0b11001, 2),
    (0b11111, 2),
];

pub struct Rmfe {
    /// `embed` of each unit vector.
    pub emb: [u64; PACK],
    /// `embed` of each value of input byte `b` (`emb8[b][v]`).
    pub emb8: [[u64; 256]; 4],
    /// Bit `i` of `project(p)` is the parity of `p & proj[i]`.
    pub proj: [u128; PACK],
    /// `embed` of all ones.
    pub ones: u64,
}

/// Built at compile time, so the kernels read it as constants.
pub static RMFE: Rmfe = Rmfe::build();

const fn deg(a: u128) -> usize {
    127 - a.leading_zeros() as usize
}

/// A carry-less product that fits in 128 bits.
const fn pmul(a: u128, b: u128) -> u128 {
    let mut p = 0;
    let mut i = 0;
    while i < 128 {
        if b >> i & 1 == 1 {
            assert!(i == 0 || a >> (128 - i) == 0);
            p ^= a << i;
        }
        i += 1;
    }
    p
}

const fn pdivmod(mut a: u128, f: u128) -> (u128, u128) {
    let mut q = 0;
    while a != 0 && deg(a) >= deg(f) {
        let s = deg(a) - deg(f);
        q |= 1 << s;
        a ^= f << s;
    }
    (q, a)
}

const fn pmod(a: u128, f: u128) -> u128 {
    pdivmod(a, f).1
}

/// The embedding of each value of the byte at bit `8 b` of the input.
const fn byte_tables(emb: &[u64; PACK]) -> [[u64; 256]; 4] {
    let mut tables = [[0u64; 256]; 4];
    let mut b = 0;
    while b < 4 {
        let mut byte = 0;
        while byte < 256 {
            let mut t = 0;
            while t < 8 {
                if byte >> t & 1 == 1 {
                    tables[b][byte] ^= emb[8 * b + t];
                }
                t += 1;
            }
            byte += 1;
        }
        b += 1;
    }
    tables
}

impl Rmfe {
    const fn build() -> Self {
        let mut modulus = 1;
        let mut held = 0;
        let mut f = 0;
        while f < FACTORS.len() {
            modulus = pmul(modulus, FACTORS[f].0);
            held += FACTORS[f].1;
            f += 1;
        }
        assert!(deg(modulus) == EMBED_BITS - 1);
        assert!(held == PACK - 1);

        let mut emb = [0u64; PACK];
        let mut proj = [0u128; PACK];
        let mut bit = 0;
        let mut i = 0;
        while i < FACTORS.len() {
            let (f, bits) = FACTORS[i];
            // The lift of a residue: 1 modulo `f`, 0 modulo the other factors.
            let (cofactor, rem) = pdivmod(modulus, f);
            assert!(rem == 0);
            let mut inv = 1;
            while pmod(pmul(pmod(cofactor, f), inv), f) != 1 {
                inv += 1;
                assert!(inv < 1 << deg(f), "coprime factors");
            }
            let lift = pmul(cofactor, inv);
            // A residue is the polynomial taking the bits as its values at 0, 1 and infinity.
            let residues: &[u128] = match bits {
                1 => &[1],
                2 => &[0b11, 0b10],
                _ => &[0b011, 0b010, 0b110],
            };
            let mut k = 0;
            while k < residues.len() {
                emb[bit + k] = pmod(pmul(pmod(lift, modulus), residues[k]), modulus) as u64;
                k += 1;
            }
            let mut c = 0;
            while c < PROD_BITS {
                let g = pmod(1 << c, f);
                let at_one = g.count_ones() as u128 & 1;
                let values: [u128; 3] = match bits {
                    1 if f == 0b10 => [g & 1, 0, 0],
                    1 => [at_one, 0, 0],
                    2 => [g & 1, at_one, 0],
                    _ => [g & 1, at_one, g >> 4],
                };
                let mut k = 0;
                while k < bits {
                    proj[bit + k] |= values[k] << c;
                    k += 1;
                }
                c += 1;
            }
            bit += bits;
            i += 1;
        }
        // The last bit rides the leading coefficient, which the residues do not see.
        emb[PACK - 1] = modulus as u64;
        proj[PACK - 1] = 1 << (PROD_BITS - 1);

        let emb8 = byte_tables(&emb);
        Self {
            emb,
            emb8,
            proj,
            ones: emb8[0][255] ^ emb8[1][255] ^ emb8[2][255] ^ emb8[3][255],
        }
    }

    #[inline(always)]
    pub fn embed(&self, a: u32) -> u64 {
        self.emb8[0][a as u8 as usize]
            ^ self.emb8[1][(a >> 8) as u8 as usize]
            ^ self.emb8[2][(a >> 16) as u8 as usize]
            ^ self.emb8[3][(a >> 24) as usize]
    }

    pub fn project(&self, product: u128) -> u32 {
        (0..PACK).fold(0, |a, i| a | (((product & self.proj[i]).count_ones() & 1) << i))
    }
}

/// lvm2 W32: the dev check (`lvm-prover w32 rmfe`): `emb`/`proj` against the Lean truth probe's literals
/// (`rmfeEmbed`/`rmfeProject` at 08645cb7), and the RMFE identity on every pair of unit vectors.
pub fn check(embed: &[u128], project: &[u128]) -> Result<(), String> {
    let r = &RMFE;
    if embed.len() != PACK || project.len() != PACK {
        return Err(format!("lengths {} {}", embed.len(), project.len()));
    }
    for i in 0..PACK {
        if r.emb[i] as u128 != embed[i] {
            return Err(format!("embed[{i}] {:#x} != Lean {:#x}", r.emb[i], embed[i]));
        }
        if r.proj[i] != project[i] {
            return Err(format!("project[{i}] {:#x} != Lean {:#x}", r.proj[i], project[i]));
        }
    }
    for i in 0..PACK {
        for j in 0..PACK {
            let p = pmul(r.emb[i] as u128, r.emb[j] as u128);
            if p >> PROD_BITS != 0 || r.project(p) != if i == j { 1 << i } else { 0 } {
                return Err(format!("identity fails at ({i}, {j})"));
            }
        }
    }
    Ok(())
}

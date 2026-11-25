//! The contract's public hashes (PROVER.md §3) and the keyed oracle hash, on leanVM's `keccak256` crate
//! (Ethereum's Keccak-256: rate 136, padding 0x01 … 0x80).

pub type Digest = [u8; 32];

pub const TAG_LEAF_ITEM: u8 = 0x48;
pub const TAG_DATA_NODE: u8 = 0x44;
pub const TAG_LEAF_STMT: u8 = 0x4C;
pub const TAG_NODE_STMT: u8 = 0x4E;

pub fn keccak256(data: &[u8]) -> Digest {
    keccak256::hash(data)
}

pub use keccak256::Hasher as Keccak256;

/// `⌊(32 + |q|)/136⌋ + 1`: the service's permutations for one keyed query.
pub fn oracle_perms(len: usize) -> u64 {
    ((32 + len) / 136 + 1) as u64
}

/// `PRF_k(q) = Keccak-256(k ‖ q)`: the hasher after the 32 key bytes, cloned per query.
#[derive(Clone)]
pub struct Keyed(Keccak256);

impl Keyed {
    pub fn new(key: &[u8; 32]) -> Self {
        let mut h = Keccak256::new();
        h.update(key);
        Self(h)
    }

    pub fn hash(&self, q: &[u8]) -> Digest {
        let mut h = self.0.clone();
        h.update(q);
        h.finalize()
    }
}

/// `leafItem x = Keccak-256(0x48 ‖ x)`.
pub fn leaf_item(x: &[u8; 32]) -> Digest {
    let mut b = [0u8; 33];
    b[0] = TAG_LEAF_ITEM;
    b[1..].copy_from_slice(x);
    keccak256(&b)
}

/// `dataNode l r = Keccak-256(0x44 ‖ l ‖ r)`.
pub fn data_node(l: &Digest, r: &Digest) -> Digest {
    let mut b = [0u8; 65];
    b[0] = TAG_DATA_NODE;
    b[1..33].copy_from_slice(l);
    b[33..].copy_from_slice(r);
    keccak256(&b)
}

/// `dataRoot xs`: leaf items, then levels of `dataNode` with an odd last digest carried up; zero for no block.
/// Leaf items and each level on the pool (each digest a function of its index: deterministic).
pub fn data_root(data: &[u8]) -> Digest {
    assert_eq!(data.len() % 32, 0, "leaf data is whole 32-byte blocks");
    let n = data.len() / 32;
    if n == 0 {
        return [0; 32];
    }
    let mut level = vec![[0u8; 32]; n];
    parallel::chunks_mut(&mut level, 4096, |c, chunk| {
        for (i, d) in chunk.iter_mut().enumerate() {
            let j = c * 4096 + i;
            *d = leaf_item(data[32 * j..32 * j + 32].try_into().unwrap());
        }
    });
    while level.len() > 1 {
        let m = level.len();
        let mut next = vec![[0u8; 32]; m.div_ceil(2)];
        let src = &level;
        parallel::chunks_mut(&mut next, 4096, |c, chunk| {
            for (i, d) in chunk.iter_mut().enumerate() {
                let j = c * 4096 + i;
                *d = if 2 * j + 1 < m { data_node(&src[2 * j], &src[2 * j + 1]) } else { src[2 * j] };
            }
        });
        level = next;
    }
    level[0]
}

/// `leafStmt h n = Keccak-256(0x4C ‖ h ‖ u64 n)`.
pub fn leaf_stmt(h: &Digest, n: u64) -> Digest {
    let mut b = [0u8; 41];
    b[0] = TAG_LEAF_STMT;
    b[1..33].copy_from_slice(h);
    b[33..].copy_from_slice(&n.to_le_bytes());
    keccak256(&b)
}

/// `nodeStmt c1 c2 = Keccak-256(0x4E ‖ c1 ‖ c2)`.
pub fn node_stmt(c1: &Digest, c2: &Digest) -> Digest {
    let mut b = [0u8; 65];
    b[0] = TAG_NODE_STMT;
    b[1..33].copy_from_slice(c1);
    b[33..].copy_from_slice(c2);
    keccak256(&b)
}

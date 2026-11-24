//! Fiat-Shamir proof transport, prover side. `add_scalar` transmits and binds together, which is the only way anything enters the state: a transmitted value needs no separate absorb, a value derived from transmitted ones needs none either, and the statement rides the seed the state starts from. So there is no absorb-only method at all. Merkle hints are authenticated by their trees and are not absorbed separately. The reading side is the `verifier` crate's transcript.

use std::marker::PhantomData;

use crate::merkle::{Hash, MerklePath, hash_to_scalars};
use crate::{FiatShamirState, Proof, Scalar, Search, grinding_bits};

// lvm6 patch (PATCHES.md, R0): a second backend, FORMAT6's hash chain over the oracle (`fs6::Transcript`), behind
// the same methods. `ProverState::new`/`from_label` keep leanVM's duplex sponge byte for byte; `ProverState::v6`
// runs every call on the chain: scalars and caps are absorbed into `BODY`, a grind is a ground group `G(max(g, 1))`
// with the least nonce, a challenge without a pending ground draw is `G(1)` (something absorbed, or no group yet) or
// a further draw `D(1)` (empty buffer inside a group), and Merkle openings go to `BODY` with V's queries recorded.
enum Backend<F> {
    Sponge(FiatShamirState<F>),
    Chain(Box<Chain6>),
}

struct Chain6 {
    t: fs6::Transcript<'static>,
    /// The challenge of a grind's ground draw, which the next `sample` returns.
    ground: Option<[u64; 2]>,
}

impl Chain6 {
    fn sample(&mut self) -> [u64; 2] {
        if let Some(e) = self.ground.take() {
            return e;
        }
        if self.t.pending() > 0 || !self.t.in_group() { self.t.ground(1) } else { self.t.draw() }
    }
}

/// Writes scalars into the stream and opening phases to the side, the stream in the verifier's field. A long grind
/// searches on `S`.
pub struct ProverState<F, S> {
    fs: Backend<F>,
    stream: Vec<verifier::E>,
    merkle: Vec<Vec<MerklePath>>,
    search: PhantomData<S>,
}

impl<F: Scalar, S: Search> ProverState<F, S> {
    /// `iv` and `public_input` seed the Fiat-Shamir state (see [`FiatShamirState::new`]).
    pub fn new(iv: [u64; 4], public_input: [u64; 4]) -> Self {
        Self::from_fs(FiatShamirState::new(iv, public_input))
    }

    /// A protocol with no public input of its own, seeded from `label` alone.
    pub fn from_label(label: &[u8]) -> Self {
        Self::from_fs(FiatShamirState::from_label(label))
    }

    fn from_fs(fs: FiatShamirState<F>) -> Self {
        Self {
            fs: Backend::Sponge(fs),
            stream: Vec::new(),
            merkle: Vec::new(),
            search: PhantomData,
        }
    }

    /// lvm6: a prover state on FORMAT6's hash chain (`t` has asked `q₀` and the seed). Puts the process in v6 mode
    /// (`fs6::set_v6(true)`): oracle Merkle trees with caps, frozen WHIR parameters, PARAM's grind rule.
    pub fn v6(t: fs6::Transcript<'static>) -> Self {
        fs6::set_v6(true);
        Self {
            fs: Backend::Chain(Box::new(Chain6 { t, ground: None })),
            stream: Vec::new(),
            merkle: Vec::new(),
            search: PhantomData,
        }
    }

    /// lvm6: `BODY` and V's queries with their answers (the `SIGN` list) of a [`Self::v6`] state.
    pub fn into_v6(self) -> (Vec<u8>, fs6::Trace) {
        match self.fs {
            Backend::Chain(c) => {
                assert!(c.ground.is_none(), "a grind is followed by a challenge");
                c.t.finish()
            }
            Backend::Sponge(_) => panic!("into_v6 of leanVM's sponge transcript"),
        }
    }

    /// lvm6: the chain transcript of a [`Self::v6`] state, if it is one.
    pub fn chain(&mut self) -> Option<&mut fs6::Transcript<'static>> {
        match &mut self.fs {
            Backend::Chain(c) => Some(&mut c.t),
            Backend::Sponge(_) => None,
        }
    }

    pub fn into_proof(self) -> Proof {
        assert!(matches!(self.fs, Backend::Sponge(_)), "a v6 state has no leanVM proof: into_v6");
        Proof {
            stream: self.stream,
            merkle_openings: self.merkle,
        }
    }

    pub fn sample(&mut self) -> F {
        match &mut self.fs {
            Backend::Sponge(fs) => fs.sample(),
            Backend::Chain(c) => F::from_limbs(c.sample()),
        }
    }

    pub fn sample_vec(&mut self, n: usize) -> Vec<F> {
        (0..n).map(|_| self.sample()).collect()
    }

    /// Hand the next opening phase's Merkle data to the verifier. Not absorbed:
    /// its binding is the Merkle structure itself.
    pub fn hint_merkle(&mut self, paths: Vec<MerklePath>) {
        match &mut self.fs {
            Backend::Sponge(_) => self.merkle.push(paths),
            Backend::Chain(c) => {
                for path in &paths {
                    let leaf: Vec<u8> = path.leaf.iter().flat_map(|w| w.0.to_le_bytes()).collect();
                    c.t.open_asked(path.leaf_index as usize, &leaf, &path.siblings);
                }
            }
        }
    }

    /// Transmit a scalar into the proof AND bind it into the state (the two are
    /// inseparable: you cannot send without binding).
    #[inline]
    pub fn add_scalar(&mut self, x: F) {
        let [c0, c1] = x.to_limbs();
        match &mut self.fs {
            Backend::Sponge(fs) => {
                fs.observe(x);
                self.stream.push(verifier::E::new(c0, c1));
            }
            Backend::Chain(c) => {
                assert!(c.ground.is_none(), "a grind is followed by a challenge");
                c.t.absorb_e(&[[c0, c1]]);
            }
        }
    }

    /// lvm6: send a commitment: leanVM's root (one digest, as [`Self::add_root`]) or FORMAT6's cap (absorbed).
    pub fn add_commitment(&mut self, commitment: &[Hash]) {
        match &mut self.fs {
            Backend::Sponge(_) => {
                assert_eq!(commitment.len(), 1, "leanVM commits to a root");
                self.add_root(&commitment[0]);
            }
            Backend::Chain(c) => c.t.absorb_cap(commitment),
        }
    }

    pub fn add_scalars(&mut self, xs: &[F]) {
        for &x in xs {
            self.add_scalar(x);
        }
    }

    /// Transmit a root as its two scalars, not as a byte string, so the recursion guest replays
    /// one shape for every digest. Sending it is what binds it: no verifier absorbs a root
    /// separately.
    pub fn add_root(&mut self, root: &Hash) {
        assert!(matches!(self.fs, Backend::Sponge(_)), "v6 commits to a cap: add_commitment");
        self.add_scalars(&hash_to_scalars(root));
    }

    /// Send one sumcheck round polynomial, as its COEFFICIENTS, constant first.
    ///
    /// The message is every coefficient but one: the running claim fixes the
    /// remaining one, which the verifier derives, so it is neither sent nor
    /// bound. Binding it would add nothing, being a function of the claim and the
    /// coefficients already bound. `eq` says whether the round's eq weight was
    /// factored out, which is what decides WHICH coefficient the claim fixes: a
    /// plain round has `h(0) + h(1) = Σ_{i≥1} c_i = claim`, which fixes `c_1`,
    /// and a round whose `eq` weight `r` was factored out has
    /// `(1 + r)·h(0) + r·h(1) = c_0 + r·Σ_{i≥1} c_i = claim`, which fixes `c_0`.
    ///
    /// Then the round's grind: the round's error is its degree over `|E|`, the degree of the whole round
    /// polynomial, eq factor included.
    pub fn add_round_poly(&mut self, coeffs: &[F], eq: bool) {
        assert!(coeffs.len() >= 2, "a round polynomial has at least two coefficients");
        let fixed = usize::from(!eq);
        for (i, &c) in coeffs.iter().enumerate() {
            if i != fixed {
                self.add_scalar(c);
            }
        }
        self.grind(grinding_bits((coeffs.len() - 1 + usize::from(eq)) as u128));
    }

    /// Proof-of-work grind of `bits` before the next challenge, which divides that verifier message's
    /// round-by-round error by `2^bits` (the prover must redo the work to re-roll it). Binds the nonce and
    /// transmits it on the stream as raw transport (already bound, so NOT re-absorbed). A grind of zero bits
    /// is nothing: no nonce, no permutation.
    pub fn grind(&mut self, bits: u32) {
        match &mut self.fs {
            Backend::Sponge(fs) => {
                if let Some(nonce) = fs.grind::<S>(bits) {
                    self.stream.push(verifier::E::new(nonce, 0));
                }
            }
            Backend::Chain(c) => {
                if bits > 0 {
                    assert!(c.ground.is_none(), "a grind is followed by a challenge");
                    c.ground = Some(c.t.ground(bits));
                }
            }
        }
    }

    /// [`Self::grind`] of `bits > 0`, then [`Self::sample`], stepping past passing nonces whose challenge is not
    /// `usable`: a verifier accepts any passing nonce.
    pub fn grind_sample(&mut self, bits: u32, usable: impl Fn(F) -> bool) -> F {
        if let Backend::Chain(c) = &mut self.fs {
            assert!(c.ground.is_none(), "a grind is followed by a challenge");
            // the least nonce whose draw passes and is usable (RT-transcript.md, Ambiguities)
            return F::from_limbs(c.t.ground_with(bits.max(1), |e| usable(F::from_limbs(e))));
        }
        let Backend::Sponge(base) = &self.fs else { unreachable!() };
        let base = base.clone();
        let mut from = 0;
        loop {
            let mut fs = base.clone();
            let nonce = fs.grind_from::<S>(bits, from).expect("a grind of nonzero bits");
            let challenge = fs.sample();
            if usable(challenge) {
                self.fs = Backend::Sponge(fs);
                self.stream.push(verifier::E::new(nonce, 0));
                return challenge;
            }
            from = nonce + 1;
        }
    }
}

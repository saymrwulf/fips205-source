// verify_mono.rs — Aeneas-compat monomorphic SLH-DSA verify path (SHA2-128s).
//
// WHY THIS FILE EXISTS (formal-verification campaign, additive & inert):
// The generic verify path threads the six hash primitives through
// `crate::hashers::Hashers`, a struct of `fn(...)` POINTERS. The Aeneas
// transpiler (Rust -> Lean 4) cannot translate function-pointer values, so
// the generic path is not directly extractable. This module reproduces the
// verify cone with:
//   (1) the hash suite reached through NAMED free functions in `oracle`
//       (marked opaque at the Charon boundary — the deliberate SHA-2
//       trust boundary of the proof), instead of fn-pointer dereferences;
//   (2) a monomorphic entry point `slh_verify_128s` fixing the SLH-DSA-
//       SHA2-128s constants.
// The const-generic function bodies are otherwise copied VERBATIM from
// wots.rs / xmss.rs / hypertree.rs / fors.rs / slh.rs so the extracted Lean
// model is faithful to the deployed algorithm. Nothing here changes the
// generic code: all twelve parameter sets are untouched, and this module is
// compiled only when the `slh_dsa_sha2_128s` feature is enabled. The unit
// test at the bottom pins fidelity by pitting this path against the
// deployed `Verifier::verify` on freshly generated signatures.
//
// This is the exact pattern used for the ed25519 verify glue
// (curve25519-dalek-source: monomorphic `verify_sha512` calling opaque
// `sha512_*` wrappers).

#![cfg(feature = "slh_dsa_sha2_128s")]
#![allow(clippy::similar_names)]
// This module is a campaign extraction root and is exercised by its own
// differential unit test; it is intentionally not called from the library's
// public API, so `dead_code` (measured from that API) does not apply.
#![allow(dead_code)]

use crate::helpers::{base_2b, to_byte, to_int};
use crate::types::{
    Adrs, ForsPk, ForsSig, HtSig, SlhDsaSig, SlhPublicKey, WotsPk, WotsSig, XmssSig, FORS_ROOTS,
    FORS_TREE, TREE, WOTS_HASH, WOTS_PK,
};

// ---------------------------------------------------------------------------
// oracle — the SHA-2 boundary, reached by name (Charon marks this module
// opaque; Aeneas emits these as opaque axioms in the Lean external model).
// Each is exactly the corresponding `sha2_cat_1` primitive; behavioural
// identity is what the differential test below checks.
// ---------------------------------------------------------------------------
pub(crate) mod oracle {
    use crate::types::Adrs;

    #[inline(never)]
    pub(crate) fn f<const N: usize>(pk_seed: &[u8], adrs: &Adrs, m1: &[u8]) -> [u8; N] {
        crate::hashers::sha2_cat_1::f::<N>(pk_seed, adrs, m1)
    }

    #[inline(never)]
    pub(crate) fn h<const N: usize>(pk_seed: &[u8], adrs: &Adrs, m1: &[u8], m2: &[u8]) -> [u8; N] {
        crate::hashers::sha2_cat_1::h::<N>(pk_seed, adrs, m1, m2)
    }

    // WOTS+ public-key compression: T_len over LEN chains (X = LEN).
    #[inline(never)]
    pub(crate) fn t_l<const X: usize, const N: usize>(
        pk_seed: &[u8], adrs: &Adrs, ml: &[[u8; N]; X],
    ) -> [u8; N] {
        crate::hashers::sha2_cat_1::t_l::<X, N>(pk_seed, adrs, ml)
    }

    // FORS root compression: T_k over K trees (X = K). Same primitive as t_l,
    // distinct call site — kept as its own name to mirror the Hashers struct.
    #[inline(never)]
    pub(crate) fn t_len<const X: usize, const N: usize>(
        pk_seed: &[u8], adrs: &Adrs, ml: &[[u8; N]; X],
    ) -> [u8; N] {
        crate::hashers::sha2_cat_1::t_l::<X, N>(pk_seed, adrs, ml)
    }

    #[inline(never)]
    pub(crate) fn h_msg<const M: usize>(
        r: &[u8], pk_seed: &[u8], pk_root: &[u8], m: &[&[u8]],
    ) -> [u8; M] {
        crate::hashers::sha2_cat_1::h_msg::<M>(r, pk_seed, pk_root, m)
    }
}

// ---------------------------------------------------------------------------
// Algorithm 5: chain — body verbatim from wots.rs::chain, hashers.f -> oracle::f.
// ---------------------------------------------------------------------------
pub(crate) fn chain_free<const N: usize>(
    cap_x: [u8; N], i: u32, s: u32, pk_seed: &[u8], adrs: &Adrs,
) -> [u8; N] {
    debug_assert!(i + s < u32::MAX);
    let mut adrs = adrs.clone();
    let mut tmp = cap_x;
    for j in i..(i + s) {
        adrs.set_hash_address(j);
        tmp = oracle::f::<N>(pk_seed, &adrs, &tmp);
    }
    tmp
}

// ---------------------------------------------------------------------------
// Algorithm 8: wots_PKFromSig — verbatim from wots.rs, hash calls -> oracle::*.
// ---------------------------------------------------------------------------
pub(crate) fn wots_pk_from_sig_free<const LEN: usize, const N: usize>(
    sig: &WotsSig<LEN, N>, m: &[u8], pk_seed: &[u8], adrs: &Adrs,
) -> WotsPk<N> {
    let n32 = u32::try_from(N).unwrap();
    let mut adrs = adrs.clone();
    let mut tmp = [[0u8; N]; LEN];

    let mut csum = 0_u32;
    let mut msg = [0u32; LEN];
    base_2b(m, crate::LGW, 2 * n32, &mut msg[0..(2 * N)]);

    for item in msg.iter().take(2 * N) {
        csum += crate::W - 1 - item;
    }

    csum <<= (8 - ((crate::LEN2 * crate::LGW) & 0x07)) & 0x07;
    base_2b(
        &to_byte(csum, (crate::LEN2 * crate::LGW + 7) / 8),
        crate::LGW,
        crate::LEN2,
        &mut msg[(2 * N)..],
    );

    #[allow(clippy::cast_possible_truncation)]
    for i in 0..LEN {
        adrs.set_chain_address(i as u32);
        tmp[i] = chain_free::<N>(
            sig.data[i],
            msg[i],
            crate::W - 1 - msg[i],
            pk_seed,
            &adrs,
        );
    }

    let mut wotspk_adrs = adrs.clone();
    wotspk_adrs.set_type_and_clear(WOTS_PK);
    wotspk_adrs.set_key_pair_address(adrs.get_key_pair_address());
    let pk = oracle::t_l::<LEN, N>(pk_seed, &wotspk_adrs, &tmp);
    WotsPk(pk)
}

// ---------------------------------------------------------------------------
// Algorithm 10: xmss_PKFromSig — verbatim from xmss.rs, hash calls -> oracle::*.
// ---------------------------------------------------------------------------
pub(crate) fn xmss_pk_from_sig_free<const HP: usize, const LEN: usize, const N: usize>(
    idx: u32, sig_xmss: &XmssSig<HP, LEN, N>, m: &[u8], pk_seed: &[u8], adrs: &Adrs,
) -> [u8; N] {
    let hp32 = u32::try_from(HP).unwrap();
    let mut adrs = adrs.clone();

    adrs.set_type_and_clear(WOTS_HASH);
    adrs.set_key_pair_address(idx);

    let sig = sig_xmss.get_wots_sig();
    let auth = sig_xmss.get_xmss_auth();

    let mut node_0 = wots_pk_from_sig_free::<LEN, N>(sig, m, pk_seed, &adrs).0;

    adrs.set_type_and_clear(TREE);
    adrs.set_tree_index(idx);

    for k in 0..hp32 {
        adrs.set_tree_height(k + 1);
        let node_1 = if ((idx >> k) & 1) == 0 {
            let tmp = adrs.get_tree_index() / 2;
            adrs.set_tree_index(tmp);
            oracle::h::<N>(pk_seed, &adrs, &node_0, &auth[k as usize])
        } else {
            let tmp = (adrs.get_tree_index() - 1) / 2;
            adrs.set_tree_index(tmp);
            oracle::h::<N>(pk_seed, &adrs, &auth[k as usize], &node_0)
        };
        node_0 = node_1;
    }

    node_0
}

// ---------------------------------------------------------------------------
// Algorithm 12: ht_verify — verbatim from hypertree.rs, calls -> *_free.
// ---------------------------------------------------------------------------
pub(crate) fn ht_verify_free<const D: usize, const HP: usize, const LEN: usize, const N: usize>(
    m: &[u8], sig_ht: &HtSig<D, HP, LEN, N>, pk_seed: &[u8], idx_tree: u64, idx_leaf: u32,
    pk_root: &[u8; N],
) -> bool {
    let mut idx_tree = idx_tree;
    let (d32, hp32) = (u32::try_from(D).unwrap(), u32::try_from(HP).unwrap());

    let mut adrs = Adrs::default();
    adrs.set_tree_address(idx_tree);

    let sig_tmp = sig_ht.xmss_sigs[0].clone();
    let mut node = xmss_pk_from_sig_free::<HP, LEN, N>(idx_leaf, &sig_tmp, m, pk_seed, &adrs);

    for j in 1..d32 {
        let idx_leaf = u32::try_from(idx_tree & ((1 << hp32) - 1));
        if idx_leaf.is_err() {
            return false;
        };
        let idx_leaf = idx_leaf.unwrap();

        idx_tree >>= hp32;

        adrs.set_layer_address(j);
        adrs.set_tree_address(idx_tree);

        let sig_tmp = sig_ht.xmss_sigs[j as usize].clone();
        node = xmss_pk_from_sig_free::<HP, LEN, N>(idx_leaf, &sig_tmp, &node, pk_seed, &adrs);
    }

    node == *pk_root // Public data, thus no CT eq required
}

// ---------------------------------------------------------------------------
// Algorithm 17: fors_pkFromSig — verbatim from fors.rs, hash calls -> oracle::*.
// ---------------------------------------------------------------------------
pub(crate) fn fors_pk_from_sig_free<const A: usize, const K: usize, const N: usize>(
    sig_fors: &ForsSig<A, K, N>, md: &[u8], pk_seed: &[u8], adrs: &Adrs,
) -> ForsPk<N> {
    let (a32, k32) = (u32::try_from(A).unwrap(), u32::try_from(K).unwrap());
    let mut adrs = adrs.clone();

    let mut indices = [0u32; K];
    base_2b(md, a32, k32, &mut indices);

    let mut root = [[0u8; N]; K];
    for i in 0..k32 {
        let sk = sig_fors.private_key_value[i as usize];

        adrs.set_tree_height(0);
        adrs.set_tree_index((i << a32) + indices[i as usize]);

        let mut node_0 = oracle::f::<N>(pk_seed, &adrs, &sk);

        let auth = sig_fors.auth[i as usize].clone();

        for j in 0..a32 {
            adrs.set_tree_height(j + 1);
            let node_1 = if ((indices[i as usize] >> j) & 0x01) == 0 {
                let tmp = adrs.get_tree_index() / 2;
                adrs.set_tree_index(tmp);
                oracle::h::<N>(pk_seed, &adrs, &node_0, &auth.tree[j as usize])
            } else {
                let tmp = (adrs.get_tree_index() - 1) / 2;
                adrs.set_tree_index(tmp);
                oracle::h::<N>(pk_seed, &adrs, &auth.tree[j as usize], &node_0)
            };
            node_0 = node_1;
        }

        root[i as usize] = node_0;
    }

    let mut fors_pk_adrs = adrs.clone();
    fors_pk_adrs.set_type_and_clear(FORS_ROOTS);
    fors_pk_adrs.set_key_pair_address(adrs.get_key_pair_address());
    let pk = oracle::t_len::<K, N>(pk_seed, &fors_pk_adrs, &root);
    ForsPk { key: pk }
}

// ---------------------------------------------------------------------------
// Algorithm 20: slh_verify_internal — verbatim from slh.rs, calls -> *_free.
// ---------------------------------------------------------------------------
#[allow(clippy::too_many_arguments, clippy::many_single_char_names)]
pub(crate) fn slh_verify_internal_free<
    const A: usize,
    const D: usize,
    const H: usize,
    const HP: usize,
    const K: usize,
    const LEN: usize,
    const M: usize,
    const N: usize,
>(
    m: &[&[u8]], sig: &SlhDsaSig<A, D, HP, K, LEN, N>, pk: &SlhPublicKey<N>,
) -> bool {
    let (d32, h32) = (u32::try_from(D).unwrap(), u32::try_from(H).unwrap());

    let mut adrs = Adrs::default();

    let r = &sig.randomness;
    let sig_fors = &sig.fors_sig;
    let sig_ht = &sig.ht_sig;

    let digest = oracle::h_msg::<M>(r, &pk.pk_seed, &pk.pk_root, m);

    let index1 = (K * A + 7) / 8;
    let md = &digest[0..index1];

    let index2 = index1 + (H - H / D + 7) / 8;
    let tmp_idx_tree = &digest[index1..index2];

    let index3 = index2 + (H + 8 * D - 1) / (8 * D);
    let tmp_idx_leaf = &digest[index2..index3];

    let idx_tree = to_int(tmp_idx_tree, (h32 - h32 / d32 + 7) / 8)
        & (u64::MAX >> (64 - (h32 - h32 / d32)));

    let idx_leaf = to_int(tmp_idx_leaf, (h32 + 8 * d32 - 1) / (8 * d32))
        & (u64::MAX >> (64 - h32 / d32));

    adrs.set_tree_address(idx_tree);
    adrs.set_type_and_clear(FORS_TREE);
    let Ok(idx_leaf_u32) = u32::try_from(idx_leaf) else { return false };
    adrs.set_key_pair_address(idx_leaf_u32);

    let pk_fors = fors_pk_from_sig_free::<A, K, N>(sig_fors, md, &pk.pk_seed, &adrs);

    ht_verify_free::<D, HP, LEN, N>(
        &pk_fors.key,
        sig_ht,
        &pk.pk_seed,
        idx_tree,
        idx_leaf_u32,
        &pk.pk_root,
    )
}

// ---------------------------------------------------------------------------
// Monomorphic entry: SLH-DSA-SHA2-128s (N=16, H=63, D=7, HP=9, A=12, K=14,
// M=30, LEN=2*N+3=35). This is the single extraction root.
// ---------------------------------------------------------------------------
pub(crate) fn slh_verify_128s(
    m: &[&[u8]], sig: &SlhDsaSig<12, 7, 9, 14, 35, 16>, pk: &SlhPublicKey<16>,
) -> bool {
    slh_verify_internal_free::<12, 7, 63, 9, 14, 35, 30, 16>(m, sig, pk)
}

// ---------------------------------------------------------------------------
// Fidelity: the monomorphic path must agree with the deployed generic
// verifier on real signatures — valid, corrupted, and wrong-message.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod tests {
    use super::slh_verify_128s;
    use crate::slh_dsa_sha2_128s::{PublicKey, KG};
    use crate::traits::{KeyGen, SerDes, Signer, Verifier};
    use crate::types::{SlhDsaSig, SlhPublicKey};
    use rand_chacha::rand_core::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    // Rebuild the pub(crate) internal structs the deployed `verify` uses
    // internally, from the public byte encodings, so the mono path can be
    // called on identical inputs.
    fn internal_inputs(
        pk: &PublicKey, sig_bytes: &[u8; 7856],
    ) -> (SlhPublicKey<16>, SlhDsaSig<12, 7, 9, 14, 35, 16>) {
        let pk_bytes = pk.clone().into_bytes();
        let mut pk_seed = [0u8; 16];
        let mut pk_root = [0u8; 16];
        pk_seed.copy_from_slice(&pk_bytes[0..16]);
        pk_root.copy_from_slice(&pk_bytes[16..32]);
        let internal_pk = SlhPublicKey { pk_seed, pk_root };
        let sig = SlhDsaSig::<12, 7, 9, 14, 35, 16>::deserialize(sig_bytes);
        (internal_pk, sig)
    }

    #[test]
    fn mono_matches_deployed_verify() {
        let mut rng = ChaCha8Rng::seed_from_u64(0xF1D5_205u64);
        for round in 0u8..3 {
            let (pk, sk) = KG::try_keygen_with_rng(&mut rng).unwrap();
            let msg = [round, 0x11, 0x22, 0x33, round.wrapping_mul(7)];

            let sig_bytes = sk.try_sign_with_rng(&mut rng, &msg, &[], false).unwrap();

            // empty-ctx M' framing, exactly as PublicKey::verify builds it
            let mp: &[&[u8]] = &[&[0u8], &[0u8], &[], &msg];

            let (internal_pk, sig) = internal_inputs(&pk, &sig_bytes);

            // 1) valid signature: deployed accepts, mono must accept, and agree
            let deployed_ok = pk.verify(&msg, &sig_bytes, &[]);
            let mono_ok = slh_verify_128s(mp, &sig, &internal_pk);
            assert!(deployed_ok, "deployed verify rejected a fresh valid signature");
            assert_eq!(mono_ok, deployed_ok, "mono disagrees with deployed on valid sig");

            // 2) corrupted signature: both must reject, together
            let mut bad_bytes = sig_bytes;
            bad_bytes[100] ^= 0x01;
            let (_, bad_sig) = internal_inputs(&pk, &bad_bytes);
            let deployed_bad = pk.verify(&msg, &bad_bytes, &[]);
            let mono_bad = slh_verify_128s(mp, &bad_sig, &internal_pk);
            assert_eq!(mono_bad, deployed_bad, "mono disagrees with deployed on corrupt sig");
            assert!(!mono_bad, "corrupt signature accepted");

            // 3) wrong message: both must reject, together
            let other = [round, 0x11, 0x22, 0x33, round.wrapping_mul(7).wrapping_add(1)];
            let mp2: &[&[u8]] = &[&[0u8], &[0u8], &[], &other];
            let deployed_wm = pk.verify(&other, &sig_bytes, &[]);
            let mono_wm = slh_verify_128s(mp2, &sig, &internal_pk);
            assert_eq!(mono_wm, deployed_wm, "mono disagrees with deployed on wrong message");
            assert!(!mono_wm, "wrong-message signature accepted");
        }
    }
}

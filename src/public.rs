#![allow(non_snake_case)]
use borsh::{BorshSerialize, BorshDeserialize};
use clear_on_drop::clear::Clear;
use curve25519_dalek::constants::{RISTRETTO_BASEPOINT_COMPRESSED, RISTRETTO_BASEPOINT_POINT};
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use rand_core::OsRng;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha512};

use zkp::{CompactProof, Transcript};

use crate::ciphertext::*;
use crate::multiply::ristretto_mul;

/// The `PublicKey` struct represents an ElGamal public key.
#[derive(Serialize, Deserialize, Copy, Clone, Debug, BorshSerialize, BorshDeserialize)]
pub struct PublicKey(RistrettoPoint);

define_proof! {dl_knowledge, "DLKnowledge Proof", (x), (A), (G) : A = (x * G)}
define_proof! {dleq, "DLEQ Proof", (x), (A, B, H), (G) : A = (x * B), H = (x * G)}

impl PublicKey {
    /// Encrypts a message in the Ristretto group. It has the additive homomorphic property,
    /// allowing addition (and subtraction) by another ciphertext and multiplication (and division)
    /// by scalars.
    ///
    /// #Example
    /// ```
    /// use rand_core::OsRng;
    /// use elgamal_ristretto::public::{PublicKey, };
    /// use elgamal_ristretto::private::{SecretKey, };
    /// use curve25519_dalek::ristretto::{RistrettoPoint, };
    /// use curve25519_dalek::scalar::{Scalar, };
    ///
    /// # fn main() {
    ///        let mut csprng = OsRng;
    ///        // Generate key pair
    ///        let sk = SecretKey::new(&mut csprng);
    ///        let pk = PublicKey::from(&sk);
    ///
    ///        // Generate random messages
    ///        let ptxt1 = RistrettoPoint::random(&mut csprng);
    ///        let ptxt2 = RistrettoPoint::random(&mut csprng);
    ///
    ///        // Encrypt messages
    ///        let ctxt1 = pk.encrypt(&ptxt1);
    ///        let ctxt2 = pk.encrypt(&ptxt2);
    ///
    ///        // Add ciphertexts and check that addition is maintained in the plaintexts
    ///        let encrypted_addition = ctxt1 + ctxt2;
    ///        let decrypted_addition = sk.decrypt(&encrypted_addition);
    ///
    ///        assert_eq!(ptxt1 + ptxt2, decrypted_addition);
    ///
    ///        // Multiply by scalar and check that multiplication is maintained in the plaintext
    ///        let scalar_mult = Scalar::random(&mut csprng);
    ///        assert_eq!(sk.decrypt(&(ctxt1 * scalar_mult)), scalar_mult * ptxt1);
    /// # }
    /// ```
    pub fn encrypt(self, message: &RistrettoPoint) -> Ciphertext {
        let mut csprng: OsRng = OsRng;
        let mut random: Scalar = Scalar::random(&mut csprng);

        let random_generator = RISTRETTO_BASEPOINT_POINT * random;
        let encrypted_plaintext = message + self.0 * random;
        random.clear();
        Ciphertext {
            pk: self,
            points: (random_generator, encrypted_plaintext),
        }
    }

    /// Encrypts a message in the Ristretto group. /!\ This function takes the passed scalar as
    /// the source of randomness for the encryption, and does not clear it after exponentiation.
    /// It has the additive homomorphic property, allowing addition (and subtraction) by another
    /// ciphertext and multiplication (and division by scalars.
    pub fn encrypt_with_random(self, message: &RistrettoPoint, random: Scalar) -> Ciphertext {
        let random_generator = RISTRETTO_BASEPOINT_POINT * random;
        let encrypted_plaintext = message + self.0 * random;
        Ciphertext {
            pk: self,
            points: (random_generator, encrypted_plaintext),
        }
    }

    /// Get the public key as a RistrettoPoint
    pub fn get_point(&self) -> RistrettoPoint {
        self.0
    }

    /// Verify EdDSA signature
    ///
    /// #Example
    /// ```
    /// use rand_core::OsRng;
    /// use elgamal_ristretto::public::{PublicKey, };
    /// use elgamal_ristretto::private::{SecretKey, };
    /// use curve25519_dalek::ristretto::RistrettoPoint;
    ///
    /// # fn main() {
    ///       // Generate key-pair
    ///       let mut csprng = OsRng;
    ///       let sk = SecretKey::new(&mut csprng);
    ///       let pk = PublicKey::from(&sk);
    ///
    ///       // Sign message
    ///       let msg = RistrettoPoint::random(&mut csprng);
    ///       let signature = sk.sign(&msg);
    ///       // Verify signature
    ///       assert!(pk.verify_signature(&msg, signature));
    ///
    ///       // Verify signature against incorrect message
    ///       assert!(!pk.verify_signature(&RistrettoPoint::random(&mut csprng), signature))
    /// # }
    /// ```
    pub fn verify_signature(
        self,
        message: &RistrettoPoint,
        signature: (Scalar, RistrettoPoint),
    ) -> bool {
        let verification_hash = Scalar::from_hash(
            Sha512::new()
                .chain(signature.1.compress().to_bytes())
                .chain(self.0.compress().to_bytes())
                .chain(message.compress().to_bytes()),
        );

        signature.0 * RISTRETTO_BASEPOINT_POINT == signature.1 + verification_hash * self.0
    }

    /// Verify proof of knowledege of private key related to a public key
    ///
    /// Example
    /// ```
    /// use rand_core::OsRng;
    /// use elgamal_ristretto::public::{PublicKey, };
    /// use elgamal_ristretto::private::{SecretKey, };
    /// use curve25519_dalek::ristretto::RistrettoPoint;
    ///
    /// # fn main() {
    ///       let mut csprng = OsRng;
    ///       let sk = SecretKey::new(&mut csprng);
    ///       let pk = PublicKey::from(&sk);
    ///
    ///       let proof = sk.prove_knowledge();
    ///       assert!(pk.verify_proof_knowledge(&proof));
    /// # }
    /// ```
    pub fn verify_proof_knowledge(self, proof: &CompactProof) -> bool {
        let mut transcript = Transcript::new(b"ProveKnowledgeSK");
        dl_knowledge::verify_compact(
            &proof,
            &mut transcript,
            dl_knowledge::VerifyAssignments {
                A: &self.0.compress(),
                G: &RISTRETTO_BASEPOINT_COMPRESSED,
            },
        )
        .is_ok()
    }

    /// Verify correct decryption
    ///
    /// Example
    /// ```
    /// use rand_core::OsRng;
    /// use elgamal_ristretto::public::{PublicKey, };
    /// use elgamal_ristretto::private::{SecretKey, };
    /// use curve25519_dalek::ristretto::RistrettoPoint;
    ///
    /// # fn main() {
    ///    let mut csprng = OsRng;
    ///    let sk = SecretKey::new(&mut csprng);
    ///    let pk = PublicKey::from(&sk);
    ///
    ///    let plaintext = RistrettoPoint::random(&mut csprng);
    ///    let ciphertext = pk.encrypt(&plaintext);
    ///
    ///    let decryption = sk.decrypt(&ciphertext);
    ///    let proof = sk.prove_correct_decryption(&ciphertext, &decryption);
    ///
    ///    assert!(pk.verify_correct_decryption(&proof, &ciphertext, &decryption));
    /// # }
    /// ```
    pub fn verify_correct_decryption(
        self,
        proof: &CompactProof,
        ciphertext: &Ciphertext,
        plaintext: &RistrettoPoint,
    ) -> bool {
        let mut transcript = Transcript::new(b"ProveCorrectDecryption");
        dleq::verify_compact(
            &proof,
            &mut transcript,
            dleq::VerifyAssignments {
                A: &(ciphertext.points.1 - plaintext).compress(),
                B: &ciphertext.points.0.compress(),
                H: &self.get_point().compress(),
                G: &RISTRETTO_BASEPOINT_COMPRESSED,
            },
        )
        .is_ok()
    }

    /// This function is only defined for testing purposes for the
    /// `prove_correct_decryption_no_Merlin`. It should not be used. If verification is
    /// performed in Rust, one should use the `prove_correct_decryption` and
    /// `verify_correct_decryption` instead.
    /// Example
    /// ```
    /// use rand_core::OsRng;
    /// use elgamal_ristretto::public::{PublicKey, };
    /// use elgamal_ristretto::private::{SecretKey, };
    /// use curve25519_dalek::ristretto::RistrettoPoint;
    ///
    /// # fn main() {
    ///    let mut csprng = OsRng;
    ///    let sk = SecretKey::new(&mut csprng);
    ///    let pk = PublicKey::from(&sk);
    ///
    ///    let plaintext = RistrettoPoint::random(&mut csprng);
    ///    let ciphertext = pk.encrypt(&plaintext);
    ///
    ///    let decryption = sk.decrypt(&ciphertext);
    ///    let proof = sk.prove_correct_decryption_no_Merlin(&ciphertext, &decryption);
    ///
    ///    assert!(pk.verify_correct_decryption_no_Merlin(&proof, &ciphertext, &decryption));
    /// # }
    /// ```
    pub fn verify_correct_decryption_no_Merlin(
        self,
        proof: &((RistrettoPoint, RistrettoPoint), Scalar),
        ciphertext: &Ciphertext,
        message: &RistrettoPoint,
    ) -> bool {
        let ((announcement_base_G, announcement_base_ctxtp0), response) = proof;
        let challenge = compute_challenge(
            &message,
            ciphertext,
            announcement_base_G,
            announcement_base_ctxtp0,
            &self,
        );
        ristretto_mul(&RISTRETTO_BASEPOINT_POINT, &response).unwrap()
            == announcement_base_G + ristretto_mul(&self.get_point(), &challenge).unwrap()
            && ristretto_mul(&ciphertext.points.0, &response).unwrap()
                == announcement_base_ctxtp0 + ristretto_mul(&(ciphertext.points.1 - message), &challenge).unwrap()
    }

    /// This function is the counterpart to prove_correct_reencryption_no_Merlin.
    /// The variable names are chosen from the point of view of the final receiver,
    /// but the verification can be performed by anyone.
    ///
    /// Source: https://crypto.stackexchange.com/questions/30010/is-there-a-way-to-prove-equality-of-plaintext-that-was-encrypted-using-different
    pub fn verify_correct_reencryption_no_Merlin(
        self,
        proof: &((RistrettoPoint, RistrettoPoint, RistrettoPoint), Scalar, Scalar),
        original_ciphertext: &Ciphertext,
        forwarded_ciphertext: &Ciphertext,
        orig_recipient_pk: &PublicKey,
    ) -> bool {
        let (
                (anncmnt_base_G_1, anncmnt_base_G_2, anncmnt_base_G_3),
                response_correct_decryption, response_correct_encryption
            ) = proof;

        let challenge = compute_challenge_ptxt_eq(
            orig_recipient_pk,
            &self,
            original_ciphertext,
            forwarded_ciphertext,
            anncmnt_base_G_1,
            anncmnt_base_G_2,
            anncmnt_base_G_3
        );

        let mut is_verified = ristretto_mul(&RISTRETTO_BASEPOINT_POINT, &response_correct_decryption).unwrap()
                                == ristretto_mul(&orig_recipient_pk.get_point(), &challenge).unwrap() + anncmnt_base_G_1;
        is_verified &= ristretto_mul(&RISTRETTO_BASEPOINT_POINT, &response_correct_encryption).unwrap()
                                == ristretto_mul(&forwarded_ciphertext.points.0, &challenge).unwrap() + anncmnt_base_G_2;
        is_verified &= *anncmnt_base_G_3
                                ==
                                    ristretto_mul(&forwarded_ciphertext.points.1, &challenge).unwrap()
                                    - ristretto_mul(&original_ciphertext.points.1, &challenge).unwrap()
                                    + ristretto_mul(&original_ciphertext.points.0, &response_correct_decryption).unwrap()
                                    - ristretto_mul(&self.0, &response_correct_encryption).unwrap();

        is_verified
    }

    /// Convert to bytes
    pub fn to_bytes(&self) -> [u8; 32] {
        self.0.compress().to_bytes()
    }

    /// Generate public key from bytes
    pub fn from_bytes(bytes: &[u8]) -> Option<PublicKey> {
        Some(PublicKey(CompressedRistretto::from_slice(bytes).decompress()?))
    }
}

/// Compute challenge for the proof of correct decryption. Used in the variation
/// that does not use Merlin.
pub(crate) fn compute_challenge(
    message: &RistrettoPoint,
    ciphertext: &Ciphertext,
    announcement_base_G: &RistrettoPoint,
    announcement_base_ctxtp0: &RistrettoPoint,
    pk: &PublicKey,
) -> Scalar {
    let mut hash = [0u8; 32];
    hash.copy_from_slice(
        solana_sdk::hash::hashv(&[
            &message.try_to_vec().unwrap(),
            &ciphertext.points.0.try_to_vec().unwrap(),
            &ciphertext.points.1.try_to_vec().unwrap(),
            &announcement_base_G.try_to_vec().unwrap(),
            &announcement_base_ctxtp0.try_to_vec().unwrap(),
            &RISTRETTO_BASEPOINT_POINT.try_to_vec().unwrap(),
            &pk.get_point().try_to_vec().unwrap(),
        ]).as_ref()
    );
    Scalar::from_bits(hash)
}

/// Compute challenge for the proof of plaintext equality. No Merlin version
/// has been implemented so far.
pub(crate) fn compute_challenge_ptxt_eq(
    orig_pk: &PublicKey,
    rnew_pk: &PublicKey,
    orig_ciphertext: &Ciphertext,
    rnew_ciphertext: &Ciphertext,
    announcement_base_G_1: &RistrettoPoint,
    announcement_base_G_2: &RistrettoPoint,
    announcement_base_G_3: &RistrettoPoint,
) -> Scalar {
    let mut hash = [0u8; 32];
    hash.copy_from_slice(
        solana_sdk::hash::hashv(&[
            &orig_ciphertext.points.1.try_to_vec().unwrap(), //c_1
            &orig_ciphertext.points.0.try_to_vec().unwrap(), //d_1
            &rnew_ciphertext.points.1.try_to_vec().unwrap(), //c_2
            &rnew_ciphertext.points.0.try_to_vec().unwrap(), //d_2
            &orig_pk.get_point().try_to_vec().unwrap(),      //g_1
            &RISTRETTO_BASEPOINT_POINT.try_to_vec().unwrap(),//h_1
            &rnew_pk.get_point().try_to_vec().unwrap(),      //g_2
            &RISTRETTO_BASEPOINT_POINT.try_to_vec().unwrap(),//h_2
            &announcement_base_G_1.try_to_vec().unwrap(),
            &announcement_base_G_2.try_to_vec().unwrap(),
            &announcement_base_G_3.try_to_vec().unwrap(),
        ]).as_ref()
    );
    Scalar::from_bits(hash)
}

impl From<RistrettoPoint> for PublicKey {
    /// Given a secret key, compute its corresponding Public key
    fn from(point: RistrettoPoint) -> PublicKey {
        PublicKey(point)
    }
}

impl PartialEq for PublicKey {
    fn eq(&self, other: &PublicKey) -> bool {
        self.0 == other.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::private::SecretKey;
    use curve25519_dalek::ristretto::CompressedRistretto;

    #[test]
    fn test_encryption() {
        let sk = SecretKey::from(Scalar::from_bytes_mod_order([
            0x90, 0x76, 0x33, 0xfe, 0x1c, 0x4b, 0x66, 0xa4, 0xa2, 0x8d, 0x2d, 0xd7, 0x67, 0x83,
            0x86, 0xc3, 0x53, 0xd0, 0xde, 0x54, 0x55, 0xd4, 0xfc, 0x9d, 0xe8, 0xef, 0x7a, 0xc3,
            0x1f, 0x35, 0xbb, 0x05,
        ]));

        let pk = PublicKey::from(&sk);

        let ptxt = CompressedRistretto([
            226, 242, 174, 10, 106, 188, 78, 113, 168, 132, 169, 97, 197, 0, 81, 95, 88, 227, 11,
            106, 165, 130, 221, 141, 182, 166, 89, 69, 224, 141, 45, 118,
        ])
        .decompress()
        .unwrap();

        let ctxt = pk.encrypt(&ptxt);
        assert_eq!(ptxt, sk.decrypt(&ctxt));
    }

    #[test]
    fn test_byte_conversion() {
        let mut csprng = OsRng;
        let sk = SecretKey::new(&mut csprng);
        let pk = PublicKey::from(&sk);

        let pk_byte = pk.to_bytes();
        let pk_from_bytes = PublicKey::from_bytes(&pk_byte).unwrap();

        assert_eq!(pk, pk_from_bytes);
    }

    #[test]
    fn test_serde_pubkey() {
        use bincode;

        let mut csprng = OsRng;
        let sk = SecretKey::new(&mut csprng);
        let pk = PublicKey::from(&sk);

        let encoded = bincode::serialize(&pk).unwrap();
        let decoded: PublicKey = bincode::deserialize(&encoded).unwrap();

        assert_eq!(pk, decoded);
    }
}

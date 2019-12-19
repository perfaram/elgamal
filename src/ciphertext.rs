use core::ops::{Add, Div, Mul, Sub};
use curve25519_dalek::ristretto::{RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use serde::{Deserialize, Serialize};

use crate::public::*;

define_proof! {dleq, "DLEQ Proof", (x), (A, B, H), (G) : A = (x * B), H = (x * G)}

#[derive(Serialize, Deserialize, Copy, Clone, Debug)]
pub struct Ciphertext {
    pub pk: PublicKey,
    pub points: (RistrettoPoint, RistrettoPoint),
}

impl Ciphertext {
    pub fn get_points(self) -> (RistrettoPoint, RistrettoPoint) {
        return (self.points.0, self.points.1);
    }
}

impl<'a, 'b> Add<&'b Ciphertext> for &'a Ciphertext {
    type Output = Ciphertext;

    fn add(self, other: &'b Ciphertext) -> Ciphertext {
        if self.pk != other.pk {
            panic!("Abort! Ciphertexts can only be added if public keys equal");
        }
        Ciphertext {
            pk: self.pk,
            points: (
                &self.points.0 + &other.points.0,
                &self.points.1 + &other.points.1,
            ),
        }
    }
}

define_add_variants!(LHS = Ciphertext, RHS = Ciphertext, Output = Ciphertext);

impl<'a, 'b> Sub<&'b Ciphertext> for &'a Ciphertext {
    type Output = Ciphertext;

    fn sub(self, other: &'b Ciphertext) -> Ciphertext {
        if self.pk != other.pk {
            panic!("Abort! Ciphertexts can only be subtracted if public keys equal");
        }
        Ciphertext {
            pk: self.pk,
            points: (
                &self.points.0 - &other.points.0,
                &self.points.1 - &other.points.1,
            ),
        }
    }
}

define_sub_variants!(LHS = Ciphertext, RHS = Ciphertext, Output = Ciphertext);

impl<'a, 'b> Mul<&'b Scalar> for &'a Ciphertext {
    type Output = Ciphertext;

    fn mul(self, other: &'b Scalar) -> Ciphertext {
        Ciphertext {
            pk: self.pk,
            points: (&self.points.0 * other, &self.points.1 * other),
        }
    }
}

define_mul_variants!(LHS = Ciphertext, RHS = Scalar, Output = Ciphertext);

impl<'a, 'b> Div<&'b Scalar> for &'a Ciphertext {
    type Output = Ciphertext;

    fn div(self, other: &'b Scalar) -> Ciphertext {
        Ciphertext {
            pk: self.pk,
            points: (
                &self.points.0 * &other.invert(),
                &self.points.1 * &other.invert(),
            ),
        }
    }
}

define_div_variants!(LHS = Ciphertext, RHS = Scalar, Output = Ciphertext);

#[cfg(test)]
mod tests {
    use super::*;
    use curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT;
    use crate::private::SecretKey;
    use rand_core::{OsRng, };

    #[test]
    fn test_homomorphic_addition() {
        let mut csprng = OsRng;
        let sk = SecretKey::new(&mut csprng);
        let pk = PublicKey::from(&sk);

        let ptxt1 = RistrettoPoint::random(&mut csprng);
        let ptxt2 = RistrettoPoint::random(&mut csprng);

        let ctxt1 = pk.encrypt(ptxt1);
        let ctxt2 = pk.encrypt(ptxt2);

        let encrypted_addition = ctxt1 + ctxt2;
        let decrypted_addition = sk.decrypt(encrypted_addition);

        assert_eq!(ptxt1 + ptxt2, decrypted_addition);
    }

    #[test]
    fn test_homomorphic_subtraction() {
        let mut csprng = OsRng;
        let sk = SecretKey::new(&mut csprng);
        let pk = PublicKey::from(&sk);

        let ptxt1 = RistrettoPoint::random(&mut csprng);
        let ptxt2 = RistrettoPoint::random(&mut csprng);

        let ctxt1 = pk.encrypt(ptxt1);
        let ctxt2 = pk.encrypt(ptxt2);

        let encrypted_addition = ctxt1 - ctxt2;
        let decrypted_addition = sk.decrypt(encrypted_addition);

        assert_eq!(ptxt1 - ptxt2, decrypted_addition);
    }

    #[test]
    fn test_multiplication_by_scalar() {
        // generates public private pair
        let mut csprng = OsRng;
        let sk = SecretKey::new(&mut csprng);
        let pk = PublicKey::from(&sk);

        let pltxt: RistrettoPoint = RistrettoPoint::random(&mut csprng);
        let enc_pltxt = pk.encrypt(pltxt);

        let mult_factor: Scalar = Scalar::random(&mut csprng);
        let mult_pltxt = pltxt * mult_factor;
        let mult_ctxt = enc_pltxt * mult_factor;
        let mult_dec_pltxt = sk.decrypt(mult_ctxt);

        assert_eq!(mult_dec_pltxt, mult_pltxt);
    }

    #[test]
    fn test_division_by_scalar() {
        let mut csprng = OsRng;
        let sk = SecretKey::new(&mut csprng);
        let pk = PublicKey::from(&sk);

        let div_factor: Scalar = Scalar::random(&mut csprng);
        let pltxt: RistrettoPoint = div_factor * RISTRETTO_BASEPOINT_POINT;
        let enc_pltxt = pk.encrypt(pltxt);

        let div_ctxt = enc_pltxt / div_factor;
        let div_dec_pltxt = sk.decrypt(div_ctxt);

        assert_eq!(div_dec_pltxt, RISTRETTO_BASEPOINT_POINT);
    }

    #[test]
    fn test_serde_ciphertext() {
        use bincode;

        let mut csprng = OsRng;
        let sk = SecretKey::new(&mut csprng);
        let pk = PublicKey::from(&sk);

        let plaintext: RistrettoPoint = RistrettoPoint::random(&mut csprng);
        let enc_plaintext = pk.encrypt(plaintext);

        let encoded = bincode::serialize(&enc_plaintext).unwrap();
        let decoded: Ciphertext = bincode::deserialize(&encoded).unwrap();

        assert_eq!(enc_plaintext.pk, decoded.pk);
        assert_eq!(enc_plaintext.points, decoded.points);
    }
}
use curve25519_dalek::{ristretto::RistrettoPoint, scalar::Scalar};
#[cfg(feature = "program")]
use solana_sdk::entrypoint::SUCCESS;
use solana_sdk::program_error::ProgramError;

/// Multiply a ristretto point with a scalar
///
/// @param point - Ristretto point
/// @param scalar - Scalar to multiply against
/// @return - result of the multiplication
#[inline]
pub fn ristretto_mul(
    point: &RistrettoPoint,
    scalar: &Scalar,
) -> Result<RistrettoPoint, ProgramError> {
    // Perform the calculation inline, calling this from within a program is
    // not supported
    #[cfg(not(all(feature = "program", target_arch = "bpf")))]
    {
        Ok(point * scalar)
    }
    // Call via a system call to perform the calculation
    #[cfg(all(feature = "program", target_arch = "bpf"))]
    {
        extern "C" {
            fn sol_ristretto_mul(
                point_addr: *const u8,
                scalar_addr: *const u8,
                result_addr: *mut u8,
            ) -> u64;
        }

        let mut result = RistrettoPoint::default();
        let status = unsafe {
            sol_ristretto_mul(
                point as *const _ as *const u8,
                scalar as *const _ as *const u8,
                &mut result as *const _ as *mut u8,
            )
        };
        match status {
            SUCCESS => Ok(result),
            _ => Err(status.into()),
        }
    }
}

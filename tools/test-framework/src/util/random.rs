/*!
   Utilities for random value generation.
*/

use ibc_relayer_types::applications::transfer::amount::Amount;
use rand::Rng;
use std::net::{Ipv4Addr, SocketAddrV4, TcpListener};

/// Generates a random `u32` value.
pub fn random_u32() -> u32 {
    let mut rng = rand::thread_rng();
    rng.gen()
}

/// Generates a random `u64` value.
pub fn random_u64() -> u64 {
    let mut rng = rand::thread_rng();
    rng.gen()
}

pub fn random_u128() -> u128 {
    let mut rng = rand::thread_rng();
    rng.gen()
}

/// Generates a random `u64` value between the given min and max.
pub fn random_u64_range(min: u64, max: u64) -> u64 {
    let mut rng = rand::thread_rng();
    rng.gen_range(min..max)
}

/// Generates a random `u128` value between the given min and max.
pub fn random_u128_range(min: u128, max: u128) -> u128 {
    let mut rng = rand::thread_rng();
    rng.gen_range(min..max)
}

pub fn random_amount_range(min: u128, max: u128) -> Amount {
    let mut rng = rand::thread_rng();
    rng.gen_range(min..max).into()
}

/// Generates a random string value, in the form of `u64` hex for simplicity.
pub fn random_string() -> String {
    format!("{:x}", random_u64())
}

/// Generates a random non-privileged port that is greater than 1024.
fn random_port() -> u16 {
    let mut rng = rand::thread_rng();
    rng.gen::<u16>()
        .checked_add(1024)
        .unwrap_or_else(random_port)
}

/// Find a random unused non-privileged TCP port.
pub fn random_unused_tcp_port() -> u16 {
    let port = random_port();
    let loopback = Ipv4Addr::new(127, 0, 0, 1);
    let address = SocketAddrV4::new(loopback, port);
    match TcpListener::bind(address) {
        Ok(_) => port,
        Err(_) => random_unused_tcp_port(),
    }
}

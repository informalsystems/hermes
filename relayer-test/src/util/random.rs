use rand::Rng;
use std::net::{Ipv4Addr, SocketAddrV4, TcpListener};

pub fn random_u32() -> u32 {
    let mut rng = rand::thread_rng();
    rng.gen()
}

pub fn random_u64() -> u64 {
    let mut rng = rand::thread_rng();
    rng.gen()
}

pub fn random_u64_range(min: u64, max: u64) -> u64 {
    let mut rng = rand::thread_rng();
    rng.gen_range(min..max)
}

pub fn random_string() -> String {
    format!("{:x}", random_u64())
}

fn random_port() -> u16 {
    let mut rng = rand::thread_rng();
    rng.gen::<u16>()
        .checked_add(1024)
        .unwrap_or_else(random_port)
}

pub fn random_unused_tcp_port() -> u16 {
    let port = random_port();
    let loopback = Ipv4Addr::new(127, 0, 0, 1);
    let address = SocketAddrV4::new(loopback, port);
    match TcpListener::bind(address) {
        Ok(_) => port,
        Err(_) => random_unused_tcp_port(),
    }
}

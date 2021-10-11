use rand::Rng;
use std::net::{SocketAddrV4, Ipv4Addr, TcpListener};

pub fn random_u32() -> u32 {
    let mut rng = rand::thread_rng();
    rng.gen()
}

fn random_port() -> u16 {
    let mut rng = rand::thread_rng();
    rng.gen::<u16>().checked_add(1024)
        .unwrap_or_else(random_port)
}

pub fn random_unused_tcp_port()
    -> u16
{
    let port = random_port();
    let loopback = Ipv4Addr::new(127, 0, 0, 1);
    let address = SocketAddrV4::new(loopback, port);
    match TcpListener::bind(address) {
        Ok(_) => port,
        Err(_) => random_unused_tcp_port()
    }
}

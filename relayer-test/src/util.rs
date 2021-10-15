use eyre::Report as Error;
use rand::Rng;
use std::fs;
use std::io;
use std::net::{Ipv4Addr, SocketAddrV4, TcpListener};
use std::thread;

pub fn random_u32() -> u32 {
    let mut rng = rand::thread_rng();
    rng.gen()
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

pub fn pipe_to_file(
    mut source: impl io::Read + Send + 'static,
    file_path: &str,
) -> Result<(), Error> {
    let mut file = fs::OpenOptions::new()
        .append(true)
        .create(true)
        .open(file_path)?;

    thread::spawn(move || {
        std::io::copy(&mut source, &mut file).unwrap();
    });

    Ok(())
}

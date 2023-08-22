use ibc_relayer::config::TracingServerConfig;
use tracing_subscriber::filter;
use tracing_subscriber::reload::Handle;
use zmq::Context;
use zmq::Message;

pub fn spawn_reload_handler(
    reload_handle: Handle<filter::EnvFilter, impl Sized>,
    tracing_server_config: TracingServerConfig,
) {
    if !tracing_server_config.enabled {
        return;
    }
    let context = Context::new();
    let responder = context.socket(zmq::REP).unwrap();

    assert!(responder
        .bind(&format!("tcp://*:{}", tracing_server_config.port))
        .is_ok());

    let mut msg = Message::new();
    loop {
        responder.recv(&mut msg, 0).unwrap();
        let cmd = msg.as_str().unwrap();
        let _ = reload_handle.reload(filter::EnvFilter::new(cmd));
        let success_msg = format!("Successfully set tracing filter to `{cmd}`");
        responder.send(success_msg.as_str(), 0).unwrap();
    }
}

pub fn send_command(cmd: String, port: u16) {
    let context = Context::new();
    let requester = context.socket(zmq::REQ).unwrap();

    assert!(requester
        .connect(&format!("tcp://localhost:{}", port))
        .is_ok());

    let mut msg = Message::new();

    requester.send(&cmd, 0).unwrap();

    requester.recv(&mut msg, 0).unwrap();
}

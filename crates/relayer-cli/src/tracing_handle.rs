use tracing_subscriber::filter;
use tracing_subscriber::reload::Handle;
use zmq::Context;
use zmq::Message;

pub fn spawn_reload_handler(reload_handle: Handle<filter::EnvFilter, impl Sized>) {
    println!("Spawning reload handler...");
    let context = Context::new();
    let responder = context.socket(zmq::REP).unwrap();

    assert!(responder.bind("tcp://*:5555").is_ok());

    let mut msg = Message::new();
    loop {
        responder.recv(&mut msg, 0).unwrap();
        let cmd = msg.as_str().unwrap();
        let _ = reload_handle.reload(filter::EnvFilter::new(cmd));
        let success_msg = format!("Successfully set tracing filter to `{cmd}`");
        responder.send(success_msg.as_str(), 0).unwrap();
    }
}

pub fn send_command(cmd: String) {
    let context = Context::new();
    let requester = context.socket(zmq::REQ).unwrap();

    assert!(requester.connect("tcp://localhost:5555").is_ok());

    let mut msg = Message::new();

    println!("Sending `{}`...", cmd);
    requester.send(&cmd, 0).unwrap();

    requester.recv(&mut msg, 0).unwrap();
    println!("{}", msg.as_str().unwrap());
}

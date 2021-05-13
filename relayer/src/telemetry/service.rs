use hyper::{
    header::CONTENT_TYPE,
    service::{make_service_fn, service_fn},
    Body, Request, Response, Server,
};

use crate::telemetry::relayer_state::RelayerState;
use opentelemetry::{global, KeyValue};
use prometheus::{Encoder, TextEncoder};
use std::convert::Infallible;
use std::sync::Arc;

lazy_static! {
    static ref HANDLER_ALL: [KeyValue; 1] = [KeyValue::new("handler", "all")];
}

pub struct TelemetryService {
    pub(crate) listen_port: u16,
}

async fn serve_req(
    _req: Request<Body>,
    state: Arc<RelayerState>,
) -> Result<Response<Body>, hyper::Error> {
    let mut buffer = vec![];
    let encoder = TextEncoder::new();
    let metric_families = state.exporter.registry().gather();
    encoder.encode(&metric_families, &mut buffer).unwrap();

    state.tx_counter.add(1);

    let response = Response::builder()
        .status(200)
        .header(CONTENT_TYPE, encoder.format_type())
        .body(Body::from(buffer))
        .unwrap();

    Ok(response)
}

impl TelemetryService {
    pub async fn run(self) -> Result<Self, Box<dyn std::error::Error + Send + Sync>> {
        let exporter = opentelemetry_prometheus::exporter().init();

        let meter = global::meter("hermes/relayer");
        let state = Arc::new(RelayerState {
            exporter,
            tx_counter: meter
                .u64_counter("hermes.tx_count")
                .with_description("Total number of transactions processed via the relayer.")
                .init()
                .bind(HANDLER_ALL.as_ref()),
        });

        // For every connection, we must make a `Service` to handle all
        // incoming HTTP requests on said connection.
        let make_svc = make_service_fn(move |_conn| {
            let state = state.clone();
            // This is the `Service` that will handle the connection.
            // `service_fn` is a helper to convert a function that
            // returns a Response into a `Service`.
            async move { Ok::<_, Infallible>(service_fn(move |req| serve_req(req, state.clone()))) }
        });

        let addr = ([127, 0, 0, 1], self.listen_port).into();

        let server = Server::bind(&addr).serve(make_svc);

        println!("Telemetry service listening on http://{}", addr);

        server.await?;

        Ok(self)
    }
}

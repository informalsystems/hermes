use alloc::sync::Arc;
use std::error::Error;
use std::net::ToSocketAddrs;

use prometheus::{Encoder, TextEncoder};
use rouille::{Request, Response, Server};

use crate::encoder::JsonEncoder;
use crate::state::TelemetryState;

enum Format {
    Text,
    Json,
}

enum Route {
    Metrics(Format),
    Other,
}

impl Route {
    fn from_request(request: &Request) -> Route {
        if request.url() == "/metrics" {
            let format = request
                .get_param("format")
                .and_then(|f| match f.as_str() {
                    "json" => Some(Format::Json),
                    "text" => Some(Format::Text),
                    _ => None,
                })
                .unwrap_or(Format::Text);

            Route::Metrics(format)
        } else {
            Route::Other
        }
    }
}

pub fn listen(
    address: impl ToSocketAddrs,
    telemetry_state: Arc<TelemetryState>,
) -> Result<Server<impl Fn(&Request) -> Response>, Box<dyn Error + Send + Sync>> {
    let server = Server::new(address, move |request| {
        match Route::from_request(request) {
            // The prometheus endpoint
            Route::Metrics(format) => {
                let mut buffer = vec![];

                match format {
                    Format::Json => {
                        let encoder = JsonEncoder::new();
                        encoder
                            .encode(&telemetry_state.gather(), &mut buffer)
                            .unwrap();

                        rouille::Response::from_data(encoder.format_type().to_string(), buffer)
                    }

                    Format::Text => {
                        let encoder = TextEncoder::new();
                        encoder
                            .encode(&telemetry_state.gather(), &mut buffer)
                            .unwrap();

                        rouille::Response::from_data(encoder.format_type().to_string(), buffer)
                    }
                }
            }

            // Any other route
            // Return an empty response with a 404 status code.
            Route::Other => rouille::Response::empty_404(),
        }
    })?;

    Ok(server)
}

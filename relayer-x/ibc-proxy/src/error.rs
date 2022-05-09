use std::fmt;

use axum::{
    http::StatusCode,
    response::{IntoResponse, Response},
};
use color_eyre::Report;

#[derive(Debug)]
pub struct ReportError(Report);

impl fmt::Display for ReportError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl From<Report> for ReportError {
    fn from(err: Report) -> Self {
        ReportError(err)
    }
}

impl IntoResponse for ReportError {
    fn into_response(self) -> Response {
        (
            StatusCode::INTERNAL_SERVER_ERROR,
            format!("Internal server error: {}", self.0),
        )
            .into_response()
    }
}

impl std::error::Error for ReportError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.0.source()
    }
}

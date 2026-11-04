// SPDX-License-Identifier: MPL-2.0
// ECHIDNA GraphQL Interface - Main server

use anyhow::Context;
use async_graphql::{EmptySubscription, Schema};
use async_graphql_axum::GraphQL;
use axum::{routing::get, Router};
use tower_http::cors::CorsLayer;

mod ffi_wrapper;
mod resolvers;
mod schema;

use resolvers::EchidnaContext;
use schema::{MutationRoot, QueryRoot};

/// Runs the GraphQL endpoint and playground at `/` and the health check at
/// `/health`, with permissive CORS. The bind address comes from
/// `ECHIDNA_GRAPHQL_ADDR`, defaulting to `127.0.0.1:8082` when it is absent.
/// Invalid configuration, bind failures and server errors are returned with
/// context. FFI initialisation failure falls back to direct Rust calls.
///
/// # Panics
///
/// Panics if logging or the HTTP client cannot be initialised.
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    tracing_subscriber::fmt()
        .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
        .init();

    let addr = match std::env::var("ECHIDNA_GRAPHQL_ADDR") {
        Ok(addr) => addr,
        Err(std::env::VarError::NotPresent) => "127.0.0.1:8082".to_string(),
        Err(error) => return Err(error).context("ECHIDNA_GRAPHQL_ADDR must be valid Unicode"),
    };
    // Bind before initialising the schema: invalid configuration is a startup
    // error, and the listener remains independent of the core server on 8081.
    // TcpListener retains support for hostname overrides such as localhost:8082.
    let listener = tokio::net::TcpListener::bind(&addr)
        .await
        .with_context(|| format!("Could not bind ECHIDNA_GRAPHQL_ADDR={addr:?}"))?;

    // Create ECHIDNA context with core integration
    let echidna_ctx = EchidnaContext::new();

    // Build GraphQL schema with ECHIDNA context
    let schema = Schema::build(QueryRoot, MutationRoot, EmptySubscription)
        .data(echidna_ctx)
        .finish();

    // Build application with routes
    let app = Router::new()
        .route(
            "/",
            get(graphql_playground).post_service(GraphQL::new(schema.clone())),
        )
        .route("/health", get(health_check))
        .layer(CorsLayer::permissive());

    tracing::info!("GraphQL server listening on http://{}", addr);
    tracing::info!("GraphQL playground available at http://{}/", addr);

    axum::serve(listener, app)
        .await
        .context("GraphQL server failed")?;
    Ok(())
}

async fn graphql_playground() -> impl axum::response::IntoResponse {
    axum::response::Html(async_graphql::http::playground_source(
        async_graphql::http::GraphQLPlaygroundConfig::new("/"),
    ))
}

async fn health_check() -> &'static str {
    "OK"
}

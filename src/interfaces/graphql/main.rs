// SPDX-License-Identifier: MPL-2.0
// ECHIDNA GraphQL Interface - Main server

use async_graphql::{EmptySubscription, Schema};
use async_graphql_axum::GraphQL;
use axum::{routing::get, Router};
use tower_http::cors::CorsLayer;

mod ffi_wrapper;
mod resolvers;
mod schema;

use resolvers::EchidnaContext;
use schema::{MutationRoot, QueryRoot};

#[tokio::main]
async fn main() {
    tracing_subscriber::fmt()
        .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
        .init();

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

    // Bind address. Default unchanged (127.0.0.1:8081) so nothing that already
    // pins it breaks, but it collides with `echidna server`, whose --port also
    // defaults to 8081: whichever starts second cannot bind. A deployment that
    // wants both on one host sets ECHIDNA_GRAPHQL_ADDR for this one, e.g.
    //   ECHIDNA_GRAPHQL_ADDR=127.0.0.1:8082 echidna-graphql
    // See docs/reports/2026-11-01-routing-and-rule-engine-recon.adoc §6 RD2 and
    // the one-port-per-project rule in standards 0-canon/PORT-REGISTRY.adoc.
    let addr =
        std::env::var("ECHIDNA_GRAPHQL_ADDR").unwrap_or_else(|_| "127.0.0.1:8081".to_string());
    tracing::info!("GraphQL server listening on http://{}", addr);
    tracing::info!("GraphQL playground available at http://{}/", addr);

    let listener = tokio::net::TcpListener::bind(&addr).await.unwrap();
    axum::serve(listener, app).await.unwrap();
}

async fn graphql_playground() -> impl axum::response::IntoResponse {
    axum::response::Html(async_graphql::http::playground_source(
        async_graphql::http::GraphQLPlaygroundConfig::new("/"),
    ))
}

async fn health_check() -> &'static str {
    "OK"
}

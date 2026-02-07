// SPDX-License-Identifier: PMPL-1.0-or-later
// ECHIDNA GraphQL Interface - Main server

use async_graphql::{Context, EmptySubscription, Object, Schema, SimpleObject};
use async_graphql_axum::GraphQL;
use axum::{routing::get, Router};
use tower_http::cors::CorsLayer;

mod schema;
mod resolvers;

use schema::{MutationRoot, QueryRoot};

#[tokio::main]
async fn main() {
    // Initialize tracing
    tracing_subscriber::fmt()
        .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
        .init();

    // Build GraphQL schema
    let schema = Schema::build(QueryRoot, MutationRoot, EmptySubscription)
        .finish();

    // Build application with routes
    let app = Router::new()
        .route("/", get(graphql_playground).post_service(GraphQL::new(schema.clone())))
        .route("/health", get(health_check))
        .layer(CorsLayer::permissive());

    // Start server
    let addr = "127.0.0.1:8080";
    tracing::info!("GraphQL server listening on http://{}", addr);
    tracing::info!("GraphQL playground available at http://{}/", addr);

    let listener = tokio::net::TcpListener::bind(addr).await.unwrap();
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

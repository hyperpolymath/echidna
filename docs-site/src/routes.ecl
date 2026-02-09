// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Route definitions for the ECHIDNA documentation site.
//!
//! Integrates with cadre-router for type-safe URL routing.

import Tea

// === Route Type ===

type Route {
    HomeRoute,
    ApiRestRoute,
    ApiGraphqlRoute,
    ApiGrpcRoute,
    ArchitectureRoute,
    CatchAll(String),
}

// === Route Parsing ===

/// Parse a URL path into a Route.
fn parse_route(path: String) -> Route {
    match path {
        "/" => HomeRoute,
        "/api/rest" => ApiRestRoute,
        "/api/graphql" => ApiGraphqlRoute,
        "/api/grpc" => ApiGrpcRoute,
        "/architecture" => ArchitectureRoute,
        other => CatchAll(other),
    }
}

/// Convert a Route to a URL path.
fn route_to_path(route: Route) -> String {
    match route {
        HomeRoute => "/",
        ApiRestRoute => "/api/rest",
        ApiGraphqlRoute => "/api/graphql",
        ApiGrpcRoute => "/api/grpc",
        ArchitectureRoute => "/architecture",
        CatchAll(path) => path,
    }
}

/// Navigate to a route (produces a command).
fn navigate_to(route: Route) -> Cmd<Msg> {
    CmdCustom { kind: "navigate", payload: route_to_path(route) }
}

// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
//! API layer - GraphQL and webhook handlers

pub mod graphql;
pub mod webhooks;

pub use graphql::create_schema;
pub use webhooks::webhook_router;

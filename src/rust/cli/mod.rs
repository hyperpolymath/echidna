// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! The `echidna` command line: argument definitions and one module per
//! command group. `main.rs` keeps only `main()`, which parses `Cli` and
//! dispatches to these.

mod args;
mod corpus;
mod design;
mod lexicon;
mod prove;
mod provers;
mod search;
mod session;
mod util;
mod verify;

pub(crate) use args::*;
pub(crate) use corpus::*;
pub(crate) use design::*;
pub(crate) use lexicon::*;
pub(crate) use prove::*;
pub(crate) use provers::*;
pub(crate) use search::*;
pub(crate) use session::*;
pub(crate) use util::*;
pub(crate) use verify::*;

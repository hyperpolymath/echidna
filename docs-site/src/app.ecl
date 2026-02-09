// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! ECHIDNA Documentation — TEA Application
//!
//! Interactive documentation viewer built with Eclexia TEA,
//! compiled to WASM for browser execution.

import Tea
import Dom

// === Model ===

type Page {
    Home,
    RestApi,
    GraphqlApi,
    GrpcApi,
    Architecture,
    NotFound(String),
}

type Model {
    current_page: Page,
    sidebar_open: Bool,
    search_query: String,
    api_explorer_visible: Bool,
}

// === Messages ===

type Msg {
    Navigate(Page),
    ToggleSidebar,
    UpdateSearch(String),
    ToggleApiExplorer,
    UrlChanged(String),
}

// === App Implementation ===

impl App for DocsApp {
    type Model = Model
    type Msg = Msg

    fn init() -> (Model, Cmd<Msg>) {
        let model = Model {
            current_page: Home,
            sidebar_open: true,
            search_query: "",
            api_explorer_visible: false,
        }
        (model, CmdNone)
    }

    fn update(model: Model, msg: Msg) -> (Model, Cmd<Msg>) {
        match msg {
            Navigate(page) => (
                Model { current_page: page, ..model },
                CmdNone,
            ),
            ToggleSidebar => (
                Model { sidebar_open: !model.sidebar_open, ..model },
                CmdNone,
            ),
            UpdateSearch(query) => (
                Model { search_query: query, ..model },
                CmdNone,
            ),
            ToggleApiExplorer => (
                Model { api_explorer_visible: !model.api_explorer_visible, ..model },
                CmdNone,
            ),
            UrlChanged(path) => {
                let page = match path {
                    "/" => Home,
                    "/api/rest" => RestApi,
                    "/api/graphql" => GraphqlApi,
                    "/api/grpc" => GrpcApi,
                    "/architecture" => Architecture,
                    other => NotFound(other),
                }
                (Model { current_page: page, ..model }, CmdNone)
            },
        }
    }

    fn view(model: Model) -> Html {
        div([("class", "docs-layout")], [
            view_sidebar(model),
            div([("class", "docs-main")], [
                view_header(model),
                view_content(model),
            ]),
        ])
    }

    fn subscriptions(model: Model) -> Sub<Msg> {
        on_event("popstate", "window", |path| UrlChanged(path))
    }
}

// === View Helpers ===

fn view_sidebar(model: Model) -> Html {
    let class = if model.sidebar_open { "sidebar open" } else { "sidebar" }
    nav([("class", class)], [
        h2([], [text("ECHIDNA")]),
        ul([], [
            nav_item("Home", Home, model.current_page),
            nav_item("REST API", RestApi, model.current_page),
            nav_item("GraphQL API", GraphqlApi, model.current_page),
            nav_item("gRPC API", GrpcApi, model.current_page),
            nav_item("Architecture", Architecture, model.current_page),
        ]),
    ])
}

fn nav_item(label: String, page: Page, current: Page) -> Html {
    let class = if page == current { "nav-item active" } else { "nav-item" }
    li([("class", class)], [
        a([("href", page_to_path(page))], [text(label)]),
    ])
}

fn view_header(model: Model) -> Html {
    div([("class", "docs-header")], [
        button([("class", "menu-toggle")], [text("Menu")]),
        div([("class", "search-bar")], [
            input([("type", "text"), ("placeholder", "Search documentation..."), ("value", model.search_query)]),
        ]),
    ])
}

fn view_content(model: Model) -> Html {
    section([("class", "docs-content")], [
        match model.current_page {
            Home => div([("id", "page-home")], [text("Welcome to ECHIDNA Documentation")]),
            RestApi => div([("id", "page-rest")], [text("REST API documentation loaded here")]),
            GraphqlApi => div([("id", "page-graphql")], [text("GraphQL API documentation loaded here")]),
            GrpcApi => div([("id", "page-grpc")], [text("gRPC API documentation loaded here")]),
            Architecture => div([("id", "page-arch")], [text("Architecture documentation loaded here")]),
            NotFound(path) => div([("id", "page-404")], [text("Page not found: " ++ path)]),
        },
    ])
}

fn page_to_path(page: Page) -> String {
    match page {
        Home => "/",
        RestApi => "/api/rest",
        GraphqlApi => "/api/graphql",
        GrpcApi => "/api/grpc",
        Architecture => "/architecture",
        NotFound(p) => p,
    }
}

// === Entry Point ===

fn main() {
    mount(DocsApp, "#app")
}

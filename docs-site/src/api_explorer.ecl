// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Interactive API Explorer for ECHIDNA documentation.
//!
//! Allows users to try API calls directly from the documentation,
//! displaying responses inline.

import Tea

// === Explorer Model ===

type ExplorerModel {
    endpoint: String,
    method: String,
    request_body: String,
    response: Option<String>,
    loading: Bool,
    error: Option<String>,
}

type ExplorerMsg {
    SetEndpoint(String),
    SetMethod(String),
    SetRequestBody(String),
    SendRequest,
    GotResponse(Result<String, String>),
    ClearResponse,
}

// === Explorer App ===

impl App for ApiExplorer {
    type Model = ExplorerModel
    type Msg = ExplorerMsg

    fn init() -> (ExplorerModel, Cmd<ExplorerMsg>) {
        let model = ExplorerModel {
            endpoint: "/api/v1/provers",
            method: "GET",
            request_body: "",
            response: None,
            loading: false,
            error: None,
        }
        (model, CmdNone)
    }

    fn update(model: ExplorerModel, msg: ExplorerMsg) -> (ExplorerModel, Cmd<ExplorerMsg>) {
        match msg {
            SetEndpoint(ep) => (
                ExplorerModel { endpoint: ep, ..model },
                CmdNone,
            ),
            SetMethod(m) => (
                ExplorerModel { method: m, ..model },
                CmdNone,
            ),
            SetRequestBody(body) => (
                ExplorerModel { request_body: body, ..model },
                CmdNone,
            ),
            SendRequest => {
                let url = "https://localhost:8000" ++ model.endpoint
                let cmd = match model.method {
                    "GET" => http_get(url, |result| GotResponse(result)),
                    "POST" => http_post(url, model.request_body, |result| GotResponse(result)),
                    _ => CmdNone,
                }
                (ExplorerModel { loading: true, error: None, ..model }, cmd)
            },
            GotResponse(result) => match result {
                Ok(body) => (
                    ExplorerModel { response: Some(body), loading: false, error: None, ..model },
                    CmdNone,
                ),
                Err(err) => (
                    ExplorerModel { response: None, loading: false, error: Some(err), ..model },
                    CmdNone,
                ),
            },
            ClearResponse => (
                ExplorerModel { response: None, error: None, ..model },
                CmdNone,
            ),
        }
    }

    fn view(model: ExplorerModel) -> Html {
        div([("class", "api-explorer")], [
            h3([], [text("API Explorer")]),
            div([("class", "explorer-controls")], [
                div([("class", "method-select")], [
                    button([("class", if model.method == "GET" { "active" } else { "" })], [text("GET")]),
                    button([("class", if model.method == "POST" { "active" } else { "" })], [text("POST")]),
                ]),
                input([("type", "text"), ("value", model.endpoint), ("placeholder", "/api/v1/...")]),
                button([("class", "send-btn")], [text(if model.loading { "Sending..." } else { "Send" })]),
            ]),
            match model.method {
                "POST" => div([("class", "request-body")], [
                    h3([], [text("Request Body")]),
                    element("textarea", [("placeholder", "{}")], [text(model.request_body)]),
                ]),
                _ => Empty,
            },
            match model.response {
                Some(body) => div([("class", "response")], [
                    h3([], [text("Response")]),
                    element("pre", [("class", "response-body")], [text(body)]),
                ]),
                None => Empty,
            },
            match model.error {
                Some(err) => div([("class", "error")], [
                    h3([], [text("Error")]),
                    p([("class", "error-text")], [text(err)]),
                ]),
                None => Empty,
            },
        ])
    }
}

# SPDX-License-Identifier: PMPL-1.0-or-later

defmodule EchidnaDocs.Router do
  @moduledoc """
  Documentation gateway router.

  Serves static files from the build directory,
  enforces capability policies, and handles AIBDP requests.
  """

  use Plug.Router

  plug(Plug.Logger)

  plug(Plug.Static,
    at: "/",
    from: {:echidna_docs, "priv/static"},
    gzip: true
  )

  plug(Plug.Static,
    at: "/.well-known",
    from: {:echidna_docs, "priv/well-known"},
    gzip: false
  )

  plug(:match)
  plug(:dispatch)

  # Health check
  get "/health" do
    send_resp(conn, 200, Jason.encode!(%{status: "ok", service: "echidna-docs"}))
  end

  # AIBDP manifest (also served via Plug.Static, but explicit route for clarity)
  get "/.well-known/aibdp.json" do
    manifest_path = Application.app_dir(:echidna_docs, "priv/well-known/aibdp.json")

    case File.read(manifest_path) do
      {:ok, content} ->
        conn
        |> put_resp_content_type("application/json")
        |> send_resp(200, content)

      {:error, _} ->
        send_resp(conn, 404, "AIBDP manifest not found")
    end
  end

  # SPA fallback — serve index.html for all unmatched routes
  match _ do
    index_path = Application.app_dir(:echidna_docs, "priv/static/index.html")

    case File.read(index_path) do
      {:ok, content} ->
        conn
        |> put_resp_content_type("text/html")
        |> send_resp(200, content)

      {:error, _} ->
        send_resp(conn, 404, "Not found")
    end
  end
end

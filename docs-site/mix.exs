# SPDX-License-Identifier: PMPL-1.0-or-later

defmodule EchidnaDocs.MixProject do
  use Mix.Project

  def project do
    [
      app: :echidna_docs,
      version: "0.1.0",
      elixir: "~> 1.17",
      start_permanent: Mix.env() == :prod,
      deps: deps()
    ]
  end

  def application do
    [
      extra_applications: [:logger],
      mod: {EchidnaDocs.Application, []}
    ]
  end

  defp deps do
    [
      {:plug_cowboy, "~> 2.7"},
      {:jason, "~> 1.4"},
      {:yaml_elixir, "~> 2.11"},
      {:req, "~> 0.5"},
      {:telemetry, "~> 1.3"}
    ]
  end
end

# echidnabot configuration in Nickel
# https://nickel-lang.org/
#
# This provides type-safe, validated configuration.
# Use: nickel export config/echidnabot.ncl > echidnabot.toml

let ProverKind = [| 'Coq, 'Lean4, 'Agda, 'Isabelle, 'Z3, 'CVC5, 'Metamath, 'HOLLight, 'Mizar |] in

let Platform = [| 'GitHub, 'GitLab, 'Bitbucket, 'Codeberg |] in

let BotMode = [| 'Verifier, 'Advisor, 'Consultant, 'Regulator |] in

let EchidnaMode = [| 'auto, 'graphql, 'rest |] in

let ServerConfig = {
  host | String | default = "0.0.0.0",
  port | Number | default = 8080,
  workers | Number | default = 4,
} in

let DatabaseConfig = {
  url | String,
  max_connections | Number | default = 10,
  min_connections | Number | default = 1,
} in

let EchidnaConfig = {
  endpoint | String,
  rest_endpoint | String,
  mode | EchidnaMode | default = 'auto,
  timeout_seconds | Number | default = 300,
  retry_attempts | Number | default = 3,
} in

let SchedulerConfig = {
  max_concurrent_jobs | Number | default = 5,
  job_timeout_seconds | Number | default = 600,
  queue_size | Number | default = 100,
} in

let LoggingConfig = {
  level | [| 'trace, 'debug, 'info, 'warn, 'error |] | default = 'info,
  format | [| 'json, 'pretty |] | default = 'json,
} in

let GitHubConfig = {
  app_id | Number | optional,
  private_key_path | String | optional,
  webhook_secret | String,
} in

let GitLabConfig = {
  token | String,
  webhook_secret | String,
} in

let ProverConfig = {
  enabled | Bool | default = true,
  timeout | Number | optional,
  flags | Array String | default = [],
} in

let Config = {
  server | ServerConfig,
  database | DatabaseConfig,
  echidna | EchidnaConfig,
  scheduler | SchedulerConfig | default = {},
  logging | LoggingConfig | default = {},
  github | GitHubConfig | optional,
  gitlab | GitLabConfig | optional,
  provers | {
    coq | ProverConfig | default = {},
    lean4 | ProverConfig | default = {},
    agda | ProverConfig | default = {},
    isabelle | ProverConfig | default = {},
    z3 | ProverConfig | default = {},
    metamath | ProverConfig | default = {},
  } | default = {},
  mode | BotMode | default = 'Verifier,
} in

# Default development configuration
{
  server = {
    host = "127.0.0.1",
    port = 8080,
    workers = 2,
  },
  database = {
    url = "sqlite://echidnabot.db",
    max_connections = 5,
  },
  echidna = {
    endpoint = "http://localhost:8080/graphql",
    rest_endpoint = "http://localhost:8080",
    mode = 'auto,
    timeout_seconds = 120,
  },
  scheduler = {
    max_concurrent_jobs = 3,
  },
  logging = {
    level = 'debug,
    format = 'pretty,
  },
  provers = {
    coq = { enabled = true },
    lean4 = { enabled = true },
    agda = { enabled = true },
    z3 = { enabled = true },
  },
  mode = 'Advisor,
} | Config

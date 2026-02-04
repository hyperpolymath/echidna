# Flush history immediately to reduce loss on crashes.
PROMPT_COMMAND="history -a${PROMPT_COMMAND:+; $PROMPT_COMMAND}"

# Optional terminal logging. Enable with: export ENABLE_TERMINAL_LOGGING=1
if [[ ${ENABLE_TERMINAL_LOGGING-} == "1" ]]; then
  "$HOME/.local/bin/terminal-recoverer" log-shell
fi

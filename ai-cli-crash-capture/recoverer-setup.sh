#!/usr/bin/env bash
set -euo pipefail

# Install paths
BIN_DIR="$HOME/.local/bin"
BASHRC_D="$HOME/.bashrc.d"
SYSTEMD_USER_DIR="$HOME/.config/systemd/user"
LOG_DIR="$HOME/Documents/terminal-logs"
CRASH_DIR="$HOME/Documents/crash-captures"

mkdir -p "$BIN_DIR" "$BASHRC_D" "$SYSTEMD_USER_DIR" "$LOG_DIR" "$CRASH_DIR"

cat > "$BIN_DIR/terminal-recoverer" <<'SCRIPT'
#!/usr/bin/env bash
set -euo pipefail

cmd=${1:-ensure}

case "$cmd" in
  ensure)
    mkdir -p "$HOME/Documents/terminal-logs"
    if command -v tmux >/dev/null 2>&1; then
      tmux has-session -t recovery 2>/dev/null || tmux new-session -d -s recovery
    fi
    ;;
  log-shell)
    # Only run in interactive terminals, and avoid recursion.
    if [[ -t 0 && -n ${PS1-} && -z ${RECOVERER_LOGGING-} ]]; then
      export RECOVERER_LOGGING=1
      mkdir -p "$HOME/Documents/terminal-logs"
      if command -v script >/dev/null 2>&1; then
        script -q -f "$HOME/Documents/terminal-logs/terminal-$(date +%F-%H%M%S).log"
      fi
    fi
    ;;
  watch-coredump)
    # Best-effort watcher for systemd-coredump messages.
    mkdir -p "$HOME/Documents/crash-captures"
    if command -v journalctl >/dev/null 2>&1; then
      journalctl -f -o cat SYSLOG_IDENTIFIER=systemd-coredump | \
        while IFS= read -r line; do
          ts=$(date +%F-%H%M%S)
          dir="$HOME/Documents/crash-captures/coredump-$ts"
          mkdir -p "$dir"
          printf "%s\n" "$line" > "$dir/journal-line.txt"
          {
            echo "time=$ts"
            echo "uname=$(uname -a)"
            echo "uptime=$(uptime -p)"
          } > "$dir/meta.txt"
          journalctl --since "2 min ago" -p err..alert --no-pager > "$dir/journal-errors.txt" 2>/dev/null || true
          journalctl --since "2 min ago" -k -p err..alert --no-pager > "$dir/journal-kernel-errors.txt" 2>/dev/null || true
          journalctl --user --since "2 min ago" -p err..alert --no-pager > "$dir/journal-user-errors.txt" 2>/dev/null || true
          journalctl --since "2 min ago" SYSLOG_IDENTIFIER=systemd-coredump --no-pager > "$dir/coredump-journal.txt" 2>/dev/null || true
          if command -v coredumpctl >/dev/null 2>&1; then
            coredumpctl --since "2 min ago" --no-pager > "$dir/coredumpctl.txt" 2>/dev/null || true
          fi
          if command -v dmesg >/dev/null 2>&1; then
            dmesg -T > "$dir/dmesg.txt" 2>/dev/null || true
          fi
          if command -v top >/dev/null 2>&1; then
            top -b -n 1 > "$dir/top.txt" 2>/dev/null || true
          fi
          if command -v ps >/dev/null 2>&1; then
            ps auxww > "$dir/ps.txt" 2>/dev/null || true
          fi
          if command -v free >/dev/null 2>&1; then
            free -h > "$dir/free.txt" 2>/dev/null || true
          fi
          if command -v df >/dev/null 2>&1; then
            df -h > "$dir/df.txt" 2>/dev/null || true
          fi
          if command -v lsblk >/dev/null 2>&1; then
            lsblk > "$dir/lsblk.txt" 2>/dev/null || true
          fi
          if command -v systemctl >/dev/null 2>&1; then
            systemctl --user --no-pager --failed > "$dir/systemd-user-failed.txt" 2>/dev/null || true
          fi
        done
    fi
    ;;
  *)
    echo "usage: terminal-recoverer [ensure|log-shell|watch-coredump]" >&2
    exit 2
    ;;
esac
SCRIPT

chmod +x "$BIN_DIR/terminal-recoverer"

cat > "$BASHRC_D/recoverer.sh" <<'SCRIPT'
# Flush history immediately to reduce loss on crashes.
PROMPT_COMMAND="history -a${PROMPT_COMMAND:+; $PROMPT_COMMAND}"

# Optional terminal logging. Enable with: export ENABLE_TERMINAL_LOGGING=1
if [[ ${ENABLE_TERMINAL_LOGGING-} == "1" ]]; then
  "$HOME/.local/bin/terminal-recoverer" log-shell
fi
SCRIPT

cat > "$SYSTEMD_USER_DIR/terminal-recoverer.service" <<'UNIT'
[Unit]
Description=Terminal recoverer (tmux session + log dir)
After=default.target

[Service]
Type=oneshot
ExecStart=%h/.local/bin/terminal-recoverer ensure

[Install]
WantedBy=default.target
UNIT

cat > "$SYSTEMD_USER_DIR/terminal-recoverer-coredump.service" <<'UNIT'
[Unit]
Description=Terminal recoverer coredump watcher (best-effort)
After=default.target

[Service]
ExecStart=%h/.local/bin/terminal-recoverer watch-coredump
Restart=always
RestartSec=2

[Install]
WantedBy=default.target
UNIT

cat > "$HOME/terminal-recoverer-HOWTO.txt" <<'TXT'
Terminal recoverer installed.

Start at login (systemd user):
  systemctl --user enable --now terminal-recoverer.service

Enable coredump watcher (best-effort):
  systemctl --user enable --now terminal-recoverer-coredump.service

Optional session logging (bash):
  export ENABLE_TERMINAL_LOGGING=1
  # add to ~/.bashrc or ~/.bash_profile if you want it always on

Using tmux recovery session:
  tmux attach -t recovery

Logs:
  ~/Documents/terminal-logs/
Crash captures:
  ~/Documents/crash-captures/
TXT

echo "Installed:"
echo "- $BIN_DIR/terminal-recoverer"
echo "- $BASHRC_D/recoverer.sh"
echo "- $SYSTEMD_USER_DIR/terminal-recoverer.service"
echo "- $SYSTEMD_USER_DIR/terminal-recoverer-coredump.service"
echo "- $HOME/terminal-recoverer-HOWTO.txt"

#!/bin/sh
# SPDX-License-Identifier: PMPL-1.0-or-later
# ECHIDNA container entrypoint

set -e

cleanup() {
    echo "Received shutdown signal — stopping echidna..."
    exit 0
}
trap cleanup TERM INT

echo "Starting echidna..."
echo "  Host: ${APP_HOST:-[::]}"
echo "  Port: ${APP_PORT:-8081}"
echo "  Data: ${APP_DATA_DIR:-/data}"
echo "  Log:  ${APP_LOG_FORMAT:-json}"

if [ -d "${APP_DATA_DIR:-/data}" ]; then
    if [ ! -w "${APP_DATA_DIR:-/data}" ]; then
        echo "WARNING: ${APP_DATA_DIR:-/data} is not writable by $(whoami)"
    fi
fi

exec /app/bin/echidna serve --host "${APP_HOST:-[::]}" --port "${APP_PORT:-8081}" "$@"

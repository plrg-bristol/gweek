#!/bin/zsh
set -e

PORT=${1:-8080}

echo "Building WASM..."
wasm-pack build --target web --out-dir web/pkg --no-typescript

echo "Serving at http://localhost:$PORT"
echo "Press Ctrl+C to stop."
open "http://localhost:$PORT"
cd web && python3 -m http.server "$PORT"

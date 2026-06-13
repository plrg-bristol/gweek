# gweek wiki — a Quartz static site over docs/, driven by bun.
#
#   just wiki-serve      preview locally with hot reload at http://localhost:8080
#   just wiki-build      emit web/wiki/ for GitHub Pages (served at /gweek/wiki)
#   just wiki-clean      remove the Quartz clone and built output
#
# Quartz is cloned into .quartz/ (gitignored) rather than vendored; our customised
# quartz.config.ts at the repo root is copied over the default before each build.

quartz_ref := "v4"
quartz_dir := ".quartz"
docs_dir   := justfile_directory() / "docs"
out_dir    := justfile_directory() / "web" / "wiki"

# List available recipes
default:
    @just --list

# Clone Quartz (pinned) and install deps with bun — idempotent
wiki-setup:
    #!/usr/bin/env bash
    set -euo pipefail
    if [ ! -d "{{quartz_dir}}/.git" ]; then
        echo "Cloning Quartz @ {{quartz_ref}} …"
        git clone --depth 1 --branch {{quartz_ref}} https://github.com/jackyzha0/quartz.git "{{quartz_dir}}"
        ( cd "{{quartz_dir}}" && bun install --frozen-lockfile )
    fi

# Preview the wiki locally with hot reload
# (bunx can't resolve Quartz's self-bin, so we invoke its bootstrap CLI directly.)
wiki-serve port="8080": wiki-setup
    cp quartz.config.ts "{{quartz_dir}}/quartz.config.ts"
    cd "{{quartz_dir}}" && bun ./quartz/bootstrap-cli.mjs build --serve --port {{port}} -d "{{docs_dir}}"

# Build the wiki into web/wiki/ (the /wiki subpath of the Pages site)
wiki-build: wiki-setup
    cp quartz.config.ts "{{quartz_dir}}/quartz.config.ts"
    cd "{{quartz_dir}}" && bun ./quartz/bootstrap-cli.mjs build -d "{{docs_dir}}" -o "{{out_dir}}"

# Remove the Quartz clone and built output
wiki-clean:
    rm -rf "{{quartz_dir}}" "{{out_dir}}"

# Justfile

# Max parallel threads for Lake/Lean builds
lean_threads := "3"

# Default task
default: build

# Build Lean library
build:
    LEAN_NUM_THREADS={{lean_threads}} lake build

# Test Lean installation
test:
    @echo "Testing Lean installation..."
    @lean --version
    @lake --version

# Clean build artifacts
clean:
    rm -rf .lake docs/book

# Update dependencies
update:
    lake update

# Generate docs/SUMMARY.md from Markdown files in docs/ and subfolders
summary:
    #!/usr/bin/env bash
    set -euo pipefail

    docs="docs"
    build_dir="$docs/book"
    out="$docs/SUMMARY.md"

    echo "# Summary" > "$out"
    echo "" >> "$out"

    # Find all .md files under docs/, excluding SUMMARY.md itself and the build output
    while IFS= read -r f; do
        rel="${f#$docs/}"

        # Skip SUMMARY.md
        [ "$rel" = "SUMMARY.md" ] && continue

        # Skip files under the build output directory
        case "$f" in "$build_dir"/*) continue ;; esac

        # Derive the title from the first H1; fallback to filename
        title="$(grep -m1 '^# ' "$f" | sed 's/^# *//')"
        if [ -z "$title" ]; then
            base="$(basename "${f%.*}")"
            title="$(printf '%s\n' "$base" \
                | tr '._-' '   ' \
                | awk '{for(i=1;i<=NF;i++){ $i=toupper(substr($i,1,1)) substr($i,2) }}1')"
        fi

        # Indent two spaces per directory depth
        depth="$(awk -F'/' '{print NF-1}' <<<"$rel")"
        indent="$(printf '%*s' $((depth*2)) '')"

        echo "${indent}- [$title](${rel})" >> "$out"
    done < <(find "$docs" -type f -name '*.md' -not -name 'SUMMARY.md' -not -path "$build_dir/*" | LC_ALL=C sort)

    echo "Wrote $out"

# Build the book after regenerating the summary
book: summary
    mdbook-mermaid install .
    mv mermaid.min.js mermaid-init.js docs/ 2>/dev/null || true
    mdbook build
    rm -f docs/mermaid-init.js docs/mermaid.min.js

# Serve locally with live reload
serve: summary
    #!/usr/bin/env bash
    trap 'echo -e "\nShutting down mdbook server..."; exit 0' INT

    mdbook-mermaid install .
    mv mermaid.min.js mermaid-init.js docs/ 2>/dev/null || true

    for port in 3000 3001 3002 3003 3004 3005; do
        if ! lsof -Pi :$port -sTCP:LISTEN -t >/dev/null 2>&1; then
            echo "Starting mdbook server on http://localhost:$port"
            mdbook serve --port $port --open
            exit 0
        fi
    done
    echo "Error: All ports 3000-3005 are already in use" >&2
    exit 1

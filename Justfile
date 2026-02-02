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
    mdbook-mermaid install . > /dev/null 2>&1 || true && cp docs/mermaid-init-patch.js mermaid-init.js && mdbook build && rm -f mermaid-init.js mermaid.min.js

# Serve locally with live reload
serve: summary
    #!/usr/bin/env bash
    trap 'rm -f mermaid-init.js mermaid.min.js' EXIT
    mdbook-mermaid install . > /dev/null 2>&1 || true && cp docs/mermaid-init-patch.js mermaid-init.js && mdbook serve --open

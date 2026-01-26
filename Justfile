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
    rm -rf .lake

# Update dependencies
update:
    lake update

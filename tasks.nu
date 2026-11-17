def main [] {
    print "usage: nu tasks.nu <task>"
    print ""
    print "tasks:"
    print "  check    evaluate the flake and run its checks"
    print "  fmt      rewrite the tree with the flake's formatters"
    print "  lean     build the Lean library"
}

# Evaluate the flake and run its checks
def "main check" [] {
    nix flake check
}

# Rewrite the tree with the flake's formatters
def "main fmt" [] {
    nix fmt
}

# Build the Lean library
def "main lean" [] {
    lake build
}

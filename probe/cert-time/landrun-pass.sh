#!/usr/bin/env bash
# H-cert probe: a stand-in for landrun (COMPARATOR_LANDRUN) that drops the sandbox arguments and runs
# the command after `--` directly. Timing only: the sandbox adds a process start, not kernel work.
while [[ $# -gt 0 && "$1" != -- ]]; do shift; done
shift
exec "$@"

#!/usr/bin/env bash

# Defaults
FILE="PrimaryBackup"
COVERAGE=1

# Parse arguments
while [[ $# -gt 0 ]]; do
  case "$1" in
    -f)
      FILE="$2"
      shift 2
      ;;
    -c)
      COVERAGE="$2"
      shift 2
      ;;
    *)
      exit 1
      ;;
  esac
done

# Build coverage flag
COVERAGE_FLAG=""
if [[ "$COVERAGE" != "0" ]]; then
  COVERAGE_FLAG="-coverage $COVERAGE"
fi

# Run TLC with debug enabled
echo '
java -agentlib:jdwp=transport=dt_socket,server=y,suspend=y,address=*:5005 \
     -XX:+UseParallelGC \
     -cp ".:./lib/tla2tools.jar" \
     tlc2.TLC \
     -config "${FILE}.cfg" \
     "${FILE}.tla" \
     -workers 1 \
     $COVERAGE_FLAG'

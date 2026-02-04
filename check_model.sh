#!/bin/bash

set -euf -o pipefail

# Build the Docker container
cd container
./run.sh << 'EOF'
cd aeron
tlc AeronRaft -config AeronRaft.cfg -workers auto -deadlock
EOF

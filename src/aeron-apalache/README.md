# AeronRaft — Apalache Port

Apalache-compatible port of `../aeron/AeronRaft.tla`. The goal is to find
invariant violations with 3 nodes using bounded model checking, where TLC's
state space is too large for BFS and simulation is too slow.

## Running

```bash
# Validate types (quick check, no model checking)
apalache-mc typecheck AeronRaft.tla

# Bounded model check — start small to validate the port
apalache-mc check --config=AeronRaft.cfg --length=10 AeronRaft.tla

# Increase depth as confidence grows
apalache-mc check --config=AeronRaft.cfg --length=30 AeronRaft.tla
apalache-mc check --config=AeronRaft.cfg --length=50 AeronRaft.tla

# Check a specific invariant
apalache-mc check --config=AeronRaft.cfg --length=30 --inv=Debug_CompleteMultipleElections AeronRaft.tla

# Use more workers / longer SMT timeout for deeper searches
apalache-mc check --config=AeronRaft.cfg --length=50 \
  --tuning-options=search.smt.timeout=3600 AeronRaft.tla
```

## Configuration

The `.cfg` is set up for 3 nodes. To test with 2 nodes first:
```
    Nodes = { N1, N2 }
```

`ArbitraryFirstLeader = N1` constrains the first election to N1, reducing the
search space (equivalent to the `UncontestedFirstElection` guard in the TLC
version).

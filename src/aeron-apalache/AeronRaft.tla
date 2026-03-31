-------------------------- MODULE AeronRaft --------------------------
\* Apalache-compatible port of the TLC version in ../aeron/AeronRaft.tla

EXTENDS Integers, FiniteSets, Sequences

\* @typeAlias: MSG = [type: Str, from: Str, to: Str, logLeadershipTermId: Int, appendPosition: Int, logPosition: Int, candidateTermId: Int, leadershipTermId: Int, nextLeadershipTermId: Int, nextTermBaseLogPosition: Int, nextLogPosition: Int, termBaseLogPosition: Int, commitPosition: Int, leaderMember: Str, vote: Int];
\* @typeAlias: LOG_ENTRY = [type: Str, payload: Str, leadershipTermId: Int, logPosition: Int, leaderMember: Str, termBaseLogPosition: Int];
\* @typeAlias: REC_ENTRY = [valid: Bool, leadershipTermId: Int, termBaseLogPosition: Int, logPosition: Int];
\* @typeAlias: REPLAY = [valid: Bool, replayPos: Int, stopPos: Int];
\* @typeAlias: REPLICATION = [valid: Bool, position: Int, stopPosition: Int, sourceMember: Str];
\* @typeAlias: SUBSCRIPTION = [valid: Bool, source: Str, position: Int];
_typedefs == TRUE

CONSTANTS
    \* @type: Set(Str);
    Nodes,
    \* @type: Set(Str);
    Payloads,
    \* @type: Str;
    Null,
    \* @type: Str;
    ArbitraryFirstLeader

VARIABLES
    \* @type: Str -> Int;
    nodeStateFile_candidateTermId,
    \* @type: Str -> Int;
    nodeStateFile_logPosition,
    \* @type: Str -> Seq(LOG_ENTRY);
    log,
    \* @type: Str -> (Int -> REC_ENTRY);
    recordingLog,
    \* @type: Str -> Str;
    role,
    \* @type: Str -> Int;
    commitPosition,
    \* @type: Str -> Str;
    leaderMember,
    \* @type: Str -> REPLAY;
    logReplay,
    \* @type: Str -> Int;
    leadershipTermId,
    \* @type: Str -> REPLICATION;
    logReplication,
    \* @type: Str -> Int;
    notifiedCommitPosition,
    \* @type: Str -> Int;
    election_replicationLeadershipTermId,
    \* @type: Str -> Int;
    election_replicationStopPosition,
    \* @type: Str -> Int;
    election_replicationTermBaseLogPosition,
    \* @type: Str -> Str;
    election_state,
    \* @type: Str -> Int;
    election_logPosition,
    \* @type: Str -> Int;
    election_appendPosition,
    \* @type: Str -> Int;
    election_logLeadershipTermId,
    \* @type: Str -> Int;
    election_leadershipTermId,
    \* @type: Str -> Int;
    election_candidateTermId,
    \* @type: Str -> Int;
    election_notifiedCommitPosition,
    \* @type: Str -> Str;
    election_leaderMember,
    \* @type: Str -> Int;
    election_catchupJoinPosition,
    \* @type: Str -> SUBSCRIPTION;
    election_logSubscription,
    \* @type: Str -> (Str -> Bool);
    clusterMembers_isBallotSent,
    \* @type: Str -> (Str -> Int);
    clusterMembers_vote,
    \* @type: Str -> (Str -> Int);
    clusterMembers_candidateTermId,
    \* @type: Str -> (Str -> Int);
    clusterMembers_leadershipTermId,
    \* @type: Str -> (Str -> Int);
    clusterMembers_logPosition,
    \* @type: <<Str, Str>> -> MSG;
    network

MaxLeadershipTerm == 2
MaxLogLength == 4

Roles == {
    "LEADER",
    "FOLLOWER",
    "CANDIDATE"
}

ElectionState == {
    "CANVASS",
    "NOMINATE",
    "CANDIDATE_BALLOT",
    "FOLLOWER_BALLOT",
    "LEADER_LOG_REPLICATION",
    "LEADER_REPLAY",
    "LEADER_INIT",
    "LEADER_READY",
    "FOLLOWER_LOG_REPLICATION",
    "FOLLOWER_REPLAY",
    "FOLLOWER_CATCHUP_INIT",
    "FOLLOWER_CATCHUP_AWAIT",
    "FOLLOWER_CATCHUP",
    "FOLLOWER_LOG_INIT",
    "FOLLOWER_LOG_AWAIT",
    "FOLLOWER_READY",
    "CLOSED"
}

MessageTypes == {
    "CanvassPosition",
    "RequestVote",
    "Vote",
    "CatchupPosition",
    "NewLeadershipTerm",
    "AppendPosition",
    "CommitPosition"
}

OptionalNode == Nodes \cup {Null}

QuorumSize == Cardinality(Nodes) \div 2 + 1

NullValue == 0 - 1

SomeValue == 1

\* Vote encoding (replaces Null/TRUE/FALSE tri-state)
VoteNull == -1
VoteTrue == 1
VoteFalse == 0

\* @type: (Int, Int) => Int;
Max2(a, b) == IF a >= b THEN a ELSE b

\* @type: (Int, Int) => Int;
Min2(a, b) == IF a <= b THEN a ELSE b

\* @type: (Set(Int)) => Int;
Max(S) == CHOOSE x \in S : \A y \in S : x >= y

\* @type: (Set(Int)) => Int;
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

\* Sentinel records for typed Null representation

\* @type: MSG;
NullMsg == [
    type |-> "Null",
    from |-> Null,
    to |-> Null,
    logLeadershipTermId |-> 0,
    appendPosition |-> 0,
    logPosition |-> 0,
    candidateTermId |-> 0,
    leadershipTermId |-> 0,
    nextLeadershipTermId |-> 0,
    nextTermBaseLogPosition |-> 0,
    nextLogPosition |-> 0,
    termBaseLogPosition |-> 0,
    commitPosition |-> 0,
    leaderMember |-> Null,
    vote |-> VoteNull
]

\* @type: LOG_ENTRY;
NullLogEntry == [type |-> "Null", payload |-> Null, leadershipTermId |-> NullValue,
                 logPosition |-> NullValue, leaderMember |-> Null, termBaseLogPosition |-> NullValue]

\* @type: REC_ENTRY;
NullRecordingEntry == [valid |-> FALSE, leadershipTermId |-> 0, termBaseLogPosition |-> 0, logPosition |-> 0]

\* @type: REPLAY;
NullReplay == [valid |-> FALSE, replayPos |-> 0, stopPos |-> 0]

\* @type: REPLICATION;
NullReplication == [valid |-> FALSE, position |-> 0, stopPosition |-> 0, sourceMember |-> Null]

\* @type: SUBSCRIPTION;
NullSubscription == [valid |-> FALSE, source |-> Null, position |-> NullValue]

Init ==
    /\ network = [src \in Nodes, dest \in Nodes |-> NullMsg]
    /\ nodeStateFile_candidateTermId = [n \in Nodes |-> NullValue]
    /\ nodeStateFile_logPosition = [n \in Nodes |-> NullValue]
    /\ log = [n \in Nodes |-> << >>]
    /\ recordingLog = [n \in Nodes |-> [i \in 0..MaxLeadershipTerm |-> NullRecordingEntry]]
    /\ role = [n \in Nodes |-> "FOLLOWER"]
    /\ commitPosition = [n \in Nodes |-> 0]
    /\ leaderMember = [n \in Nodes |-> Null]
    /\ logReplay = [n \in Nodes |-> NullReplay]
    /\ leadershipTermId = [n \in Nodes |-> NullValue]
    /\ logReplication = [n \in Nodes |-> NullReplication]
    /\ notifiedCommitPosition = [n \in Nodes |-> 0]
    /\ election_state = [n \in Nodes |-> "CANVASS"]
    /\ election_logPosition = [n \in Nodes |-> 0]
    /\ election_appendPosition = [n \in Nodes |-> 0]
    /\ election_logLeadershipTermId = [n \in Nodes |-> NullValue]
    /\ election_leadershipTermId = [n \in Nodes |-> NullValue]
    /\ election_candidateTermId = [n \in Nodes |-> NullValue]
    /\ election_notifiedCommitPosition = [n \in Nodes |-> 0]
    /\ election_leaderMember = [n \in Nodes |-> Null]
    /\ election_catchupJoinPosition = [n \in Nodes |-> NullValue]
    /\ election_logSubscription = [n \in Nodes |-> NullSubscription]
    /\ election_replicationLeadershipTermId = [n \in Nodes |-> NullValue]
    /\ election_replicationStopPosition = [n \in Nodes |-> NullValue]
    /\ election_replicationTermBaseLogPosition = [n \in Nodes |-> NullValue]
    /\ clusterMembers_vote = [n \in Nodes |-> [m \in Nodes |-> VoteNull]]
    /\ clusterMembers_candidateTermId = [n \in Nodes |-> [m \in Nodes |-> NullValue]]
    /\ clusterMembers_isBallotSent = [n \in Nodes |-> [m \in Nodes |-> FALSE]]
    /\ clusterMembers_leadershipTermId = [n \in Nodes |-> [m \in Nodes |-> NullValue]]
    /\ clusterMembers_logPosition = [n \in Nodes |-> [m \in Nodes |-> IF m = n THEN 0 ELSE NullValue]]

\* Tuple aliases removed — Apalache needs individual variables in UNCHANGED clauses

vars == <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_state, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition, clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition, network>>

\* Send with unicast-style backpressure
\* @type: (<<Str, Str>> -> MSG, MSG) => Bool;
Send(newNetwork, msg) ==
    /\ newNetwork[msg.from, msg.to].type = "Null"
    /\ network' = [newNetwork EXCEPT ![msg.from, msg.to] = msg]

\* Send with mc-max-fc-style backpressure (rewritten without @@)
\* @type: (<<Str, Str>> -> MSG, MSG) => Bool;
Broadcast(newNetwork, msg) ==
    LET destinations == { d \in Nodes : d /= msg.from /\ newNetwork[msg.from, d].type = "Null" }
    IN /\ destinations /= {}
       /\ network' = [src \in Nodes, dest \in Nodes |->
            IF src = msg.from /\ dest \in destinations
            THEN [msg EXCEPT !.to = dest]
            ELSE newNetwork[src, dest]]

HasMessage(src, dest, type) ==
    network[src, dest].type = type

ConsumeMessage(src, dest) == [network EXCEPT ![src, dest] = NullMsg]

OtherNodes(n) == Nodes \ {n}

ResetUnusedFields(n) ==
    /\ election_replicationStopPosition' = [election_replicationStopPosition EXCEPT ![n] = NullValue]
    /\ election_replicationLeadershipTermId' = [election_replicationLeadershipTermId EXCEPT ![n] = NullValue]
    /\ election_replicationTermBaseLogPosition' = [election_replicationTermBaseLogPosition EXCEPT ![n] = NullValue]
    /\ election_logSubscription' = [election_logSubscription EXCEPT ![n] = NullSubscription]
    /\ election_catchupJoinPosition' = [election_catchupJoinPosition EXCEPT ![n] = NullValue]
    /\ logReplication' = [logReplication EXCEPT ![n] = NullReplication]
    /\ logReplay' = [logReplay EXCEPT ![n] = NullReplay]

ResetElectionFields(n) ==
    /\ election_logPosition' = [election_logPosition EXCEPT ![n] = 0]
    /\ election_appendPosition' = [election_appendPosition EXCEPT ![n] = 0]
    /\ election_logLeadershipTermId' = [election_logLeadershipTermId EXCEPT ![n] = NullValue]
    /\ election_leadershipTermId' = [election_leadershipTermId EXCEPT ![n] = NullValue]
    /\ election_candidateTermId' = [election_candidateTermId EXCEPT ![n] = NullValue]
    /\ election_notifiedCommitPosition' = [election_notifiedCommitPosition EXCEPT ![n] = 0]
    /\ election_leaderMember' = [election_leaderMember EXCEPT ![n] = Null]
    /\ election_catchupJoinPosition' = [election_catchupJoinPosition EXCEPT ![n] = NullValue]
    /\ election_replicationStopPosition' = [election_replicationStopPosition EXCEPT ![n] = NullValue]
    /\ election_replicationLeadershipTermId' = [election_replicationLeadershipTermId EXCEPT ![n] = NullValue]
    /\ election_replicationTermBaseLogPosition' = [election_replicationTermBaseLogPosition EXCEPT ![n] = NullValue]
    /\ logReplication' = [logReplication EXCEPT ![n] = NullReplication]
    /\ logReplay' = [logReplay EXCEPT ![n] = NullReplay]
    /\ clusterMembers_isBallotSent' = [ clusterMembers_isBallotSent EXCEPT ![n] = [ m \in Nodes |-> FALSE ] ]
    /\ clusterMembers_vote' = [ clusterMembers_vote EXCEPT ![n] = [ m \in Nodes |-> VoteNull ] ]

Election_State_CANVASS(n, timeoutCount) ==
    /\ election_state' = [election_state EXCEPT ![n] = "CANVASS"]
    /\ clusterMembers_isBallotSent' = [ clusterMembers_isBallotSent EXCEPT ![n] = [ m \in Nodes |-> FALSE ] ]
    /\ clusterMembers_vote' = [ clusterMembers_vote EXCEPT ![n] = [ m \in Nodes |-> VoteNull ] ]
    /\ clusterMembers_candidateTermId' = [ clusterMembers_candidateTermId EXCEPT ![n] = [ m \in Nodes |-> NullValue ] ]
    /\ clusterMembers_leadershipTermId' = [ clusterMembers_leadershipTermId EXCEPT ![n] =
                                                 [ m \in Nodes |-> IF m = n THEN election_leadershipTermId[n] ELSE NullValue ] ]
    /\ clusterMembers_logPosition' = [ clusterMembers_logPosition EXCEPT ![n] =
                                                 [ m \in Nodes |-> IF m = n THEN election_logPosition[n] ELSE NullValue ] ]
    /\ election_leaderMember' = [election_leaderMember EXCEPT ![n] = Null]
    /\ role' = [role EXCEPT ![n] = "FOLLOWER"]
    /\ ResetUnusedFields(n)

Election_State_CANDIDATE_BALLOT(n) ==
    /\ election_state' = [election_state EXCEPT ![n] = "CANDIDATE_BALLOT"]
    /\ role' = [role EXCEPT ![n] = "CANDIDATE"]

Election_State_LEADER_LOG_REPLICATION(n) ==
    /\ election_state' = [election_state EXCEPT ![n] = "LEADER_LOG_REPLICATION"]
    /\ role' = [role EXCEPT ![n] = "LEADER"]

Election_State_FOLLOWER_LOG_REPLICATION(n) ==
    /\ election_state' = [election_state EXCEPT ![n] = "FOLLOWER_LOG_REPLICATION"]
    /\ role' = [role EXCEPT ![n] = "FOLLOWER"]

Election_State_FOLLOWER_REPLAY(n) ==
    /\ election_state' = [election_state EXCEPT ![n] = "FOLLOWER_REPLAY"]
    /\ role' = [role EXCEPT ![n] = "FOLLOWER"]

Election_HandleError(n) ==
    /\ election_logPosition' = [election_logPosition EXCEPT ![n] = commitPosition[n]]
    /\ Election_State_CANVASS(n, 1)
    /\ election_notifiedCommitPosition' = [election_candidateTermId EXCEPT ![n] = 0]
    /\ election_candidateTermId' = [election_candidateTermId EXCEPT ![n] = Max2(nodeStateFile_candidateTermId[n], election_leadershipTermId[n])]
    /\ election_appendPosition' = [election_appendPosition EXCEPT ![n] = Len(log[n])]
    /\ commitPosition' = [commitPosition EXCEPT ![n] = election_logPosition[n]]

Election_PublishCanvassPosition(n) ==
    /\ Broadcast(network, [NullMsg EXCEPT
            !.type = "CanvassPosition",
            !.from = n,
            !.logLeadershipTermId = election_logLeadershipTermId[n],
            !.appendPosition = election_appendPosition[n],
            !.logPosition = election_logPosition[n]])
    /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_state, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition, clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition>>

\* @type: (Int, Int, Int, Int) => Int;
ClusterMember_CompareLog0(lhsLeadershipTermId, lhsLogPosition, rhsLeadershipTermId, rhsLogPosition) ==
    IF lhsLeadershipTermId > rhsLeadershipTermId THEN 1
    ELSE IF lhsLeadershipTermId < rhsLeadershipTermId THEN NullValue
    ELSE IF lhsLogPosition > rhsLogPosition THEN 1
    ELSE IF lhsLogPosition < rhsLogPosition THEN NullValue
    ELSE 0

ClusterMember_CompareLog1(perspective, candidate, other) ==
    ClusterMember_CompareLog0(
        clusterMembers_leadershipTermId[perspective][candidate],
        clusterMembers_logPosition[perspective][candidate],
        clusterMembers_leadershipTermId[perspective][other],
        clusterMembers_logPosition[perspective][other])

ClusterMember_WillVoteFor(perspective, candidate, other) ==
    /\ clusterMembers_logPosition[perspective][other] /= NullValue
    /\ ClusterMember_CompareLog1(perspective, candidate, other) <= 0

Election_Canvass(n) ==
    /\ election_state[n] = "CANVASS"
    /\ \/ Election_PublishCanvassPosition(n)
       \/ /\ Cardinality({m \in Nodes : ClusterMember_WillVoteFor(n, n, m)}) >= QuorumSize
          /\ election_state' = [election_state EXCEPT ![n] = "NOMINATE"]
          /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition, clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition, network>>

NodeStateFile_ProposeMaxCandidateTermId(n, candidateTermId, logPosition) ==
    LET newCandidateTermId == Max2(candidateTermId, nodeStateFile_candidateTermId[n])
        newLogPosition == IF candidateTermId > nodeStateFile_candidateTermId[n] THEN logPosition ELSE nodeStateFile_logPosition[n]
    IN /\ newCandidateTermId <= MaxLeadershipTerm \* STATE SPACE GUARD
       /\ nodeStateFile_candidateTermId' = [nodeStateFile_candidateTermId EXCEPT ![n] = newCandidateTermId ]
       /\ nodeStateFile_logPosition' = [nodeStateFile_logPosition EXCEPT ![n] = newLogPosition]
       /\ election_candidateTermId' = [election_candidateTermId EXCEPT ![n] = newCandidateTermId]

ClusterMember_BecomeCandidate(n, candidateTermId) ==
    /\ clusterMembers_isBallotSent' = [ clusterMembers_isBallotSent EXCEPT ![n] = [ m \in Nodes |-> n = m ] ]
    /\ clusterMembers_candidateTermId' = [ clusterMembers_candidateTermId EXCEPT ![n] = [ m \in Nodes |-> IF n = m THEN candidateTermId ELSE NullValue ] ]
    /\ clusterMembers_vote' = [ clusterMembers_vote EXCEPT ![n] = [ m \in Nodes |-> IF n = m THEN VoteTrue ELSE VoteNull ] ]

Election_Nominate(n) ==
    /\ election_state[n] = "NOMINATE"
    /\ \/ Election_PublishCanvassPosition(n)
       \/ LET newCandidateTermId == Max2(election_candidateTermId[n] + 1, nodeStateFile_candidateTermId[n])
          IN /\ newCandidateTermId <= MaxLeadershipTerm \* STATE SPACE GUARD
             /\ \/ n = ArbitraryFirstLeader \* STATE SPACE GUARD
                \/ leadershipTermId[n] >= 0 \* STATE SPACE GUARD
             /\ NodeStateFile_ProposeMaxCandidateTermId(n, newCandidateTermId, election_logPosition[n])
             /\ ClusterMember_BecomeCandidate(n, newCandidateTermId)
             /\ Election_State_CANDIDATE_BALLOT(n)
             /\ UNCHANGED <<log, recordingLog, commitPosition, leaderMember, logReplay,
                            leadershipTermId, logReplication, notifiedCommitPosition,
                            election_logPosition, election_appendPosition,
                            election_logLeadershipTermId, election_leadershipTermId, election_notifiedCommitPosition,
                            election_leaderMember,
                            election_catchupJoinPosition, election_logSubscription,
                            election_replicationLeadershipTermId, election_replicationStopPosition,
                            election_replicationTermBaseLogPosition,
                            clusterMembers_leadershipTermId, clusterMembers_logPosition, network>>

IsQuorumLeader(n) ==
    /\ Cardinality({ m \in Nodes: clusterMembers_vote[n][m] = VoteTrue}) >= QuorumSize
    /\ \A m \in Nodes : clusterMembers_vote[n][m] /= VoteFalse

Election_CandidateBallot(n) ==
    /\ election_state[n] = "CANDIDATE_BALLOT"
    /\ \/ /\ IsQuorumLeader(n)
          /\ election_leaderMember' = [ election_leaderMember EXCEPT ![n] = n ]
          /\ election_leadershipTermId' = [ election_leadershipTermId EXCEPT ![n] = election_candidateTermId[n] ]
          /\ Election_State_LEADER_LOG_REPLICATION(n)
          /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, commitPosition, leaderMember, logReplay, leadershipTermId,
                         logReplication, notifiedCommitPosition,
                         election_logPosition, election_appendPosition,
                         election_logLeadershipTermId, election_candidateTermId, election_notifiedCommitPosition,
                         election_catchupJoinPosition, election_logSubscription,
                         election_replicationLeadershipTermId, election_replicationStopPosition,
                         election_replicationTermBaseLogPosition,
                         clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition, network>>
       \/ /\ Election_State_CANVASS(n, 1)
          /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, commitPosition, leaderMember, leadershipTermId,
                         notifiedCommitPosition,
                         election_logPosition, election_appendPosition, election_logLeadershipTermId,
                         election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition,
                         network>>
       \/ /\ \A m \in OtherNodes(n) : clusterMembers_isBallotSent[n][m] = FALSE
          /\ Broadcast(network, [NullMsg EXCEPT
                  !.type = "RequestVote",
                  !.from = n,
                  !.logLeadershipTermId = election_logLeadershipTermId[n],
                  !.logPosition = election_appendPosition[n],
                  !.candidateTermId = election_candidateTermId[n]])
          /\ clusterMembers_isBallotSent' = [clusterMembers_isBallotSent EXCEPT ![n] = [m \in Nodes |-> TRUE]]
          /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_state, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition,
                         clusterMembers_vote, clusterMembers_candidateTermId,
                         clusterMembers_leadershipTermId, clusterMembers_logPosition>>

Election_FollowerBallot(n) ==
    /\ election_state[n] = "FOLLOWER_BALLOT"
    /\ Election_State_CANVASS(n, 1)
    /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, commitPosition, leaderMember, leadershipTermId,
                   notifiedCommitPosition,
                   election_logPosition, election_appendPosition, election_logLeadershipTermId,
                   election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, network>>

\* MaxQuorumPosition: find the QuorumSize-th largest position (rewritten without SetToSeq/SortSeq)
MaxQuorumPosition(n) ==
    LET quorumPositions == { p \in { clusterMembers_logPosition[n][m] : m \in Nodes } :
            Cardinality({ m \in Nodes : clusterMembers_logPosition[n][m] >= p }) >= QuorumSize }
    IN Max(quorumPositions)

\* @type: (REPLICATION) => Bool;
LogReplication_IsDone(replication) ==
    replication.valid /\ replication.position >= replication.stopPosition

\* @type: (REPLAY) => Bool;
LogReplay_IsDone(replay) ==
    replay.valid /\ replay.replayPos >= replay.stopPos

RecordingLog_FindTermEntry(n, termId) ==
    IF termId \in 0..MaxLeadershipTerm /\ recordingLog[n][termId].valid
    THEN recordingLog[n][termId]
    ELSE NullRecordingEntry

\* Rewritten for fixed-domain recordingLog (replaces dynamic DOMAIN + growing functions)
RecordingLog_EnsureCoherent(n, termId, termBaseLogPosition, logPosition) ==
    LET existingTerms == { i \in 0..MaxLeadershipTerm : recordingLog[n][i].valid }
        maxExistingTerm == IF existingTerms = {} THEN -1 ELSE Max(existingTerms)
        maxTerm == Max2(maxExistingTerm, termId)
    IN recordingLog' = [recordingLog EXCEPT ![n] =
        [i \in 0..MaxLeadershipTerm |->
            IF i > maxTerm THEN
                recordingLog[n][i]
            ELSE IF i = maxExistingTerm /\ maxExistingTerm >= 0 /\ recordingLog[n][i].logPosition = NullValue THEN
                [recordingLog[n][i] EXCEPT !.logPosition = termBaseLogPosition]
            ELSE IF i <= maxExistingTerm /\ recordingLog[n][i].valid THEN
                recordingLog[n][i]
            ELSE IF i < termId THEN
                [valid |-> TRUE, leadershipTermId |-> i,
                 termBaseLogPosition |-> termBaseLogPosition,
                 logPosition |-> termBaseLogPosition]
            ELSE
                [valid |-> TRUE, leadershipTermId |-> i,
                 termBaseLogPosition |-> termBaseLogPosition,
                 logPosition |-> logPosition]
        ]
    ]

Election_OnReplayNewLeadershipTermEvent(n, termId, logPosition_param, termBaseLogPosition) ==
    /\ RecordingLog_EnsureCoherent(n, termId, termBaseLogPosition, NullValue)
    /\ election_logPosition' = [election_logPosition EXCEPT ![n] = logPosition_param]
    /\ election_logLeadershipTermId' = [election_logLeadershipTermId EXCEPT ![n] = termId]

CM_OnReplayNewLeadershipTermEvent(n, termId, logPosition_param, termBaseLogPosition) ==
    /\ leadershipTermId' = [leadershipTermId EXCEPT ![n] = termId]
    /\ \/ /\ election_state[n] \in {"FOLLOWER_CATCHUP", "FOLLOWER_REPLAY"}
          /\ Election_OnReplayNewLeadershipTermEvent(n, termId, logPosition_param, termBaseLogPosition)
       \/ /\ election_state[n] \notin {"FOLLOWER_CATCHUP", "FOLLOWER_REPLAY"}
          /\ UNCHANGED <<recordingLog, election_logPosition, election_logLeadershipTermId>>

Election_PublishNewLeadershipTermOnInterval(n, quorumPos) ==
    /\ LET entry == RecordingLog_FindTermEntry(n, election_leadershipTermId[n]) IN
       LET nextLeadershipTermId == IF ~entry.valid THEN election_leadershipTermId[n] ELSE entry.leadershipTermId + 1 IN
       LET nextTermBaseLogPosition == IF ~entry.valid THEN election_appendPosition[n] ELSE entry.termBaseLogPosition IN
       LET nextLogPosition == IF ~entry.valid THEN NullValue
                              ELSE IF entry.logPosition = NullValue THEN election_appendPosition[n]
                              ELSE entry.logPosition IN
       Broadcast(network, [NullMsg EXCEPT
                           !.type = "NewLeadershipTerm",
                           !.from = n,
                           !.logLeadershipTermId = election_logLeadershipTermId[n],
                           !.nextLeadershipTermId = nextLeadershipTermId,
                           !.nextTermBaseLogPosition = nextTermBaseLogPosition,
                           !.nextLogPosition = nextLogPosition,
                           !.leadershipTermId = election_leadershipTermId[n],
                           !.termBaseLogPosition = election_appendPosition[n],
                           !.logPosition = election_appendPosition[n],
                           !.commitPosition = quorumPos,
                           !.leaderMember = n ])

CM_PublishCommitPosition(n, quorumPos, termId) ==
    Broadcast(network, [NullMsg EXCEPT
                        !.type = "CommitPosition",
                        !.from = n,
                        !.leadershipTermId = termId,
                        !.logPosition = quorumPos,
                        !.leaderMember = n ])

Election_PublishCommitPositionOnInterval(n, quorumPos) ==
    CM_PublishCommitPosition(n, quorumPos, election_leadershipTermId[n])

CM_QuorumPositionBoundedByLeaderLog0(n, leaderAppendPosition) ==
    Min2(leaderAppendPosition, MaxQuorumPosition(n))

CM_QuorumPositionBoundedByLeaderLog1(n) ==
    CM_QuorumPositionBoundedByLeaderLog0(n, election_appendPosition[n])

Election_LeaderLogReplication(n) ==
    /\ election_state[n] = "LEADER_LOG_REPLICATION"
    /\ clusterMembers_logPosition' = [ clusterMembers_logPosition EXCEPT ![n][n] = election_appendPosition[n]]
    /\ LET quorumPos == CM_QuorumPositionBoundedByLeaderLog1(n)
       IN \/ /\ quorumPos >= election_appendPosition[n]
             /\ election_state' = [ election_state EXCEPT ![n] = "LEADER_REPLAY" ]
             /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition, clusterMembers_vote,
                            clusterMembers_candidateTermId, clusterMembers_isBallotSent,
                            clusterMembers_leadershipTermId, network>>
          \/ /\ Election_PublishNewLeadershipTermOnInterval(n, quorumPos)
             /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_state, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition,
                            clusterMembers_vote, clusterMembers_candidateTermId,
                            clusterMembers_isBallotSent, clusterMembers_leadershipTermId>>
          \/ /\ Election_PublishCommitPositionOnInterval(n, quorumPos)
             /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_state,
                            election_logPosition, election_appendPosition,
                            election_logLeadershipTermId, election_leadershipTermId,
                            election_candidateTermId, election_notifiedCommitPosition,
                            election_leaderMember,
                            election_catchupJoinPosition, election_logSubscription,
                            election_replicationLeadershipTermId, election_replicationStopPosition,
                            election_replicationTermBaseLogPosition,
                            clusterMembers_vote, clusterMembers_candidateTermId,
                            clusterMembers_isBallotSent, clusterMembers_leadershipTermId>>

Election_LeaderReplay(n) ==
    /\ election_state[n] = "LEADER_REPLAY"
    /\ \/ /\ ~logReplay[n].valid
          /\ clusterMembers_leadershipTermId' = [ clusterMembers_leadershipTermId EXCEPT ![n][n] = election_leadershipTermId[n] ]
          /\ clusterMembers_logPosition' = [ clusterMembers_logPosition EXCEPT ![n][n] = election_appendPosition[n] ]
          /\ \/ /\ election_appendPosition[n] > election_logPosition[n]
                /\ logReplay' = [ logReplay EXCEPT ![n] = [ valid |-> TRUE, replayPos |-> election_logPosition[n], stopPos |-> election_appendPosition[n] ] ]
                /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId,
                               notifiedCommitPosition,
                               logReplication, election_state, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition,
                               clusterMembers_vote, clusterMembers_candidateTermId,
                               clusterMembers_isBallotSent, network>>
             \/ /\ election_appendPosition[n] <= election_logPosition[n]
                /\ election_state' = [ election_state EXCEPT ![n] = "LEADER_INIT" ]
                /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition,
                               clusterMembers_vote, clusterMembers_candidateTermId,
                               clusterMembers_isBallotSent, network>>
       \/ /\ logReplay[n].valid
          /\ logReplay[n].stopPos <= logReplay[n].replayPos
          /\ logReplay' = [ logReplay EXCEPT ![n] = NullReplay ]
          /\ election_logPosition' = [ election_logPosition EXCEPT ![n] = election_appendPosition[n] ]
          /\ election_state' = [ election_state EXCEPT ![n] = "LEADER_INIT" ]
          /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId,
                         notifiedCommitPosition,
                         logReplication, election_appendPosition,
                         election_logLeadershipTermId, election_leadershipTermId,
                         election_candidateTermId, election_notifiedCommitPosition,
                         election_leaderMember,
                         election_catchupJoinPosition, election_logSubscription,
                         election_replicationLeadershipTermId, election_replicationStopPosition,
                         election_replicationTermBaseLogPosition,
                         clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition, network>>
       \/ /\ Election_PublishNewLeadershipTermOnInterval(n, CM_QuorumPositionBoundedByLeaderLog1(n))
          /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_state, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition, clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition>>
       \/ /\ Election_PublishCommitPositionOnInterval(n, CM_QuorumPositionBoundedByLeaderLog1(n))
          /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_state,
                         election_logPosition, election_appendPosition,
                         election_logLeadershipTermId, election_leadershipTermId,
                         election_candidateTermId, election_notifiedCommitPosition,
                         election_leaderMember,
                         election_catchupJoinPosition, election_logSubscription,
                         election_replicationLeadershipTermId, election_replicationStopPosition,
                         election_replicationTermBaseLogPosition,
                         clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition>>

Election_LeaderInit(n) ==
    /\ election_state[n] = "LEADER_INIT"
    /\ election_logLeadershipTermId' = [election_logLeadershipTermId EXCEPT ![n] = election_leadershipTermId[n]]
    /\ leadershipTermId' = [leadershipTermId EXCEPT ![n] = election_leadershipTermId[n]]
    /\ RecordingLog_EnsureCoherent(n, election_leadershipTermId[n], election_appendPosition[n], election_logPosition[n])
    /\ election_state' = [election_state EXCEPT ![n] = "LEADER_READY"]
    /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log,
                   role, commitPosition, leaderMember, logReplay, logReplication,
                   notifiedCommitPosition,
                   election_logPosition, election_appendPosition,
                   election_leadershipTermId, election_candidateTermId,
                   election_notifiedCommitPosition,
                   election_leaderMember, election_catchupJoinPosition, election_logSubscription,
                   election_replicationLeadershipTermId, election_replicationStopPosition,
                   election_replicationTermBaseLogPosition,
                   clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition, network>>

ClusterMember_HasQuorumAtPosition(n) ==
    Cardinality({ m \in Nodes: /\ clusterMembers_leadershipTermId[n][m] = election_leadershipTermId[n]
                               /\ clusterMembers_logPosition[n][m] >= election_logPosition[n]}) >= QuorumSize

CM_UpdateLeaderPosition(n, appendPos, quorumPos) ==
    /\ clusterMembers_logPosition' = [clusterMembers_logPosition EXCEPT ![n][n] = appendPos]
    /\ \/ /\ quorumPos > commitPosition[n]
          /\ CM_PublishCommitPosition(n, quorumPos, leadershipTermId[n])
          /\ commitPosition' = [commitPosition EXCEPT ![n] = quorumPos]
          /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, leaderMember, logReplay, leadershipTermId,
                         logReplication, notifiedCommitPosition,
                         election_state, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition,
                         clusterMembers_vote, clusterMembers_candidateTermId,
                         clusterMembers_isBallotSent, clusterMembers_leadershipTermId>>
       \/ /\ quorumPos <= commitPosition[n]
          /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_state, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition,
                         clusterMembers_vote, clusterMembers_candidateTermId,
                         clusterMembers_isBallotSent, clusterMembers_leadershipTermId, network>>

CM_ElectionComplete(n) ==
    /\ leadershipTermId' = [leadershipTermId EXCEPT ![n] = election_leadershipTermId[n]]
    /\ commitPosition' = [commitPosition EXCEPT ![n] = election_logPosition[n]]
    /\ notifiedCommitPosition' = [notifiedCommitPosition EXCEPT ![n] = Max2(election_logPosition[n], notifiedCommitPosition[n])]
    /\ leaderMember' = [leaderMember EXCEPT ![n] = election_leaderMember[n]]
    /\ ResetElectionFields(n)

Election_LeaderReady(n) ==
    /\ election_state[n] = "LEADER_READY"
    /\ LET quorumPos == CM_QuorumPositionBoundedByLeaderLog1(n)
       IN \/ /\ ClusterMember_HasQuorumAtPosition(n)
             /\ CM_ElectionComplete(n)
             /\ Len(log[n]) < MaxLogLength \* STATE SPACE GUARD
             /\ log' = [log EXCEPT ![n] = Append(@, [
                    type |-> "NewLeadershipTerm",
                    payload |-> Null,
                    leadershipTermId |-> election_leadershipTermId[n],
                    logPosition |-> election_logPosition[n],
                    leaderMember |-> n,
                    termBaseLogPosition |-> election_appendPosition[n]
                ])]
             /\ election_state' = [election_state EXCEPT ![n] = "CLOSED"]
             /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, recordingLog,
                            role, election_logSubscription, clusterMembers_candidateTermId,
                            clusterMembers_leadershipTermId, clusterMembers_logPosition,
                            network>>
          \/ CM_UpdateLeaderPosition(n, election_appendPosition[n], quorumPos)
          \/ /\ Election_PublishNewLeadershipTermOnInterval(n, quorumPos)
             /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_state, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition, clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition>>

Election_PublishFollowerReplicationPosition(n) ==
    /\ Send(network, [NullMsg EXCEPT
                      !.type = "AppendPosition",
                      !.from = n,
                      !.to = election_leaderMember[n],
                      !.leadershipTermId = election_replicationLeadershipTermId[n],
                      !.logPosition = election_appendPosition[n],
                      !.leaderMember = election_leaderMember[n]])
    /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_state,
                   election_logPosition, election_appendPosition,
                   election_logLeadershipTermId, election_leadershipTermId,
                   election_candidateTermId, election_notifiedCommitPosition,
                   election_leaderMember,
                   election_catchupJoinPosition, election_logSubscription,
                   election_replicationLeadershipTermId, election_replicationStopPosition,
                   election_replicationTermBaseLogPosition,
                   clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition>>

Election_PublishFollowerAppendPosition(n) ==
    /\ Send(network, [NullMsg EXCEPT
                      !.type = "AppendPosition",
                      !.from = n,
                      !.to = election_leaderMember[n],
                      !.leadershipTermId = election_leadershipTermId[n],
                      !.logPosition = election_appendPosition[n],
                      !.leaderMember = election_leaderMember[n]])
    /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_state,
                   election_logPosition, election_appendPosition,
                   election_logLeadershipTermId, election_leadershipTermId,
                   election_candidateTermId, election_notifiedCommitPosition,
                   election_leaderMember,
                   election_catchupJoinPosition, election_logSubscription,
                   election_replicationLeadershipTermId, election_replicationStopPosition,
                   election_replicationTermBaseLogPosition,
                   clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition>>

Election_FollowerLogReplication(n) ==
    /\ election_state[n] = "FOLLOWER_LOG_REPLICATION"
    /\ \/ /\ ~logReplication[n].valid
          /\ \/ /\ election_appendPosition[n] < election_replicationStopPosition[n]
                /\ logReplication' = [logReplication EXCEPT ![n] = [
                       valid |-> TRUE,
                       position |-> election_appendPosition[n],
                       stopPosition |-> election_replicationStopPosition[n],
                       sourceMember |-> election_leaderMember[n]
                   ]]
                /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, logReplay,
                               leadershipTermId, notifiedCommitPosition, election_state,
                               election_logPosition, election_appendPosition,
                               election_logLeadershipTermId, election_leadershipTermId,
                               election_candidateTermId, election_notifiedCommitPosition, election_leaderMember,
                               election_catchupJoinPosition, election_logSubscription,
                               election_replicationStopPosition, election_replicationLeadershipTermId, election_replicationTermBaseLogPosition,
                               clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition, network>>
             \/ /\ election_appendPosition[n] >= election_replicationStopPosition[n]
                /\ RecordingLog_EnsureCoherent(n, election_replicationLeadershipTermId[n], election_replicationTermBaseLogPosition[n], election_replicationStopPosition[n])
                /\ election_logLeadershipTermId' = [election_logLeadershipTermId EXCEPT ![n] = election_replicationLeadershipTermId[n]]
                /\ Election_State_CANVASS(n, 0)
                /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log,
                               commitPosition, leaderMember, leadershipTermId,
                               notifiedCommitPosition,
                               election_logPosition, election_appendPosition, election_leadershipTermId,
                               election_candidateTermId, election_notifiedCommitPosition, network>>
       \/ /\ logReplication[n].valid
          /\ ~LogReplication_IsDone(logReplication[n])
          /\ LET newPosition == logReplication[n].position + 1
                 sourceMember == logReplication[n].sourceMember
                 sourceLogLength == Len(log[sourceMember])
             IN /\ sourceLogLength >= newPosition
                /\ newPosition <= MaxLogLength \* STATE SPACE GUARD
                /\ logReplication' = [logReplication EXCEPT ![n].position = newPosition]
                /\ log' = [log EXCEPT ![n] = Append(@, log[sourceMember][newPosition])]
                /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, recordingLog,
                               role, commitPosition, leaderMember, logReplay,
                               leadershipTermId, notifiedCommitPosition, election_state, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition,
                               clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition, network>>
       \/ /\ LogReplication_IsDone(logReplication[n])
          /\ election_notifiedCommitPosition[n] >= election_appendPosition[n]
          /\ election_appendPosition' = [election_appendPosition EXCEPT ![n] = logReplication[n].position]
          /\ RecordingLog_EnsureCoherent(n, election_replicationLeadershipTermId[n], election_replicationTermBaseLogPosition[n], election_replicationStopPosition[n])
          /\ election_logLeadershipTermId' = [election_logLeadershipTermId EXCEPT ![n] = election_replicationLeadershipTermId[n]]
          /\ Election_State_CANVASS(n, 0)
          /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log,
                         commitPosition, leaderMember, leadershipTermId,
                         notifiedCommitPosition,
                         election_logPosition, election_leadershipTermId,
                         election_candidateTermId, election_notifiedCommitPosition, network>>
       \/ /\ logReplication[n].valid
          /\ Election_PublishFollowerReplicationPosition(n)
       \/ /\ LogReplication_IsDone(logReplication[n])
          /\ election_notifiedCommitPosition[n] < election_appendPosition[n]
          /\ Election_HandleError(n)
          /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, leaderMember, leadershipTermId,
                         notifiedCommitPosition, election_logLeadershipTermId, election_leadershipTermId, network>>

Election_FollowerReplay(n) ==
    /\ election_state[n] = "FOLLOWER_REPLAY"
    /\ \/ /\ ~logReplay[n].valid
          /\ \/ /\ election_logPosition[n] < election_appendPosition[n]
                /\ election_notifiedCommitPosition[n] = 0
                /\ Election_PublishFollowerAppendPosition(n)
             \/ /\ election_logPosition[n] < election_appendPosition[n]
                /\ election_notifiedCommitPosition[n] /= 0
                /\ election_logPosition[n] >= election_notifiedCommitPosition[n]
                /\ Election_State_CANVASS(n, 0)
                /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, commitPosition, leaderMember, leadershipTermId,
                               notifiedCommitPosition,
                               election_logPosition, election_appendPosition, election_logLeadershipTermId,
                               election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition,
                               network>>
             \/ /\ election_logPosition[n] < election_appendPosition[n]
                /\ election_notifiedCommitPosition[n] /= 0
                /\ election_logPosition[n] < election_notifiedCommitPosition[n]
                /\ logReplay' = [logReplay EXCEPT ![n] = [
                       valid |-> TRUE,
                       replayPos |-> election_logPosition[n],
                       stopPos |-> Min2(election_appendPosition[n], election_notifiedCommitPosition[n])
                   ]]
                /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId,
                               logReplication, notifiedCommitPosition, election_state,
                               election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition, clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition, network>>
             \/ /\ election_logPosition[n] >= election_appendPosition[n]
                /\ election_state' = [election_state EXCEPT ![n] =
                       IF election_catchupJoinPosition[n] /= NullValue
                       THEN "FOLLOWER_CATCHUP_INIT"
                       ELSE "FOLLOWER_LOG_INIT"]
                /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition, clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition, network>>
       \/ /\ logReplay[n].valid
          /\ ~LogReplay_IsDone(logReplay[n])
          /\ LET currentPos == logReplay[n].replayPos + 1
                 logEntry == IF Len(log[n]) >= currentPos THEN log[n][currentPos] ELSE NullLogEntry
             IN /\ logEntry.type /= "Null"
                /\ logReplay' = [logReplay EXCEPT ![n].replayPos = currentPos]
                /\ commitPosition' = [commitPosition EXCEPT ![n] = Max2(commitPosition[n], currentPos)]
                /\ \/ /\ logEntry.type = "NewLeadershipTerm"
                      /\ CM_OnReplayNewLeadershipTermEvent(n, logEntry.leadershipTermId, logEntry.logPosition, logEntry.termBaseLogPosition)
                      /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log,
                                     role, leaderMember, logReplication, notifiedCommitPosition,
                                     election_state, election_appendPosition, election_leadershipTermId,
                                     election_candidateTermId, election_notifiedCommitPosition,
                                     election_leaderMember,
                                     election_catchupJoinPosition, election_logSubscription,
                                     election_replicationLeadershipTermId, election_replicationStopPosition,
                                     election_replicationTermBaseLogPosition,
                                     clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition, network>>
                   \/ /\ logEntry.type /= "NewLeadershipTerm"
                      /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, leaderMember, leadershipTermId, logReplication,
                                     notifiedCommitPosition,
                                     election_state, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition, clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition, network>>
       \/ /\ LogReplay_IsDone(logReplay[n])
          /\ election_logPosition' = [election_logPosition EXCEPT ![n] = logReplay[n].replayPos]
          /\ logReplay' = [logReplay EXCEPT ![n] = NullReplay]
          /\ \/ /\ logReplay[n].replayPos = election_appendPosition[n]
                /\ election_catchupJoinPosition[n] /= NullValue
                /\ election_state' = [election_state EXCEPT ![n] = "FOLLOWER_CATCHUP_INIT"]
                /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId,
                               logReplication, notifiedCommitPosition,
                               election_appendPosition, election_logLeadershipTermId,
                               election_leadershipTermId, election_candidateTermId,
                               election_notifiedCommitPosition,
                               election_leaderMember, election_catchupJoinPosition, election_logSubscription,
                               election_replicationLeadershipTermId, election_replicationStopPosition,
                               election_replicationTermBaseLogPosition,
                               clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition, network>>
             \/ /\ logReplay[n].replayPos = election_appendPosition[n]
                /\ election_catchupJoinPosition[n] = NullValue
                /\ election_state' = [election_state EXCEPT ![n] = "FOLLOWER_LOG_INIT"]
                /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId,
                               logReplication, notifiedCommitPosition,
                               election_appendPosition, election_logLeadershipTermId,
                               election_leadershipTermId, election_candidateTermId,
                               election_notifiedCommitPosition,
                               election_leaderMember, election_catchupJoinPosition, election_logSubscription,
                               election_replicationLeadershipTermId, election_replicationStopPosition,
                               election_replicationTermBaseLogPosition,
                               clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition, network>>
             \/ /\ logReplay[n].replayPos /= election_appendPosition[n]
                /\ Election_State_CANVASS(n, 1)
                /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition,
                               election_appendPosition, election_logLeadershipTermId,
                               election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition,
                               network>>

Election_FollowerCatchupInit(n) ==
    /\ election_state[n] = "FOLLOWER_CATCHUP_INIT"
    /\ \/ /\ election_leaderMember[n] /= Null
          /\ election_logSubscription' = [election_logSubscription EXCEPT ![n] = [ valid |-> TRUE,
                                                                                   source |-> election_leaderMember[n],
                                                                                   position |-> NullValue ] ]
          /\ Send(network, [NullMsg EXCEPT
                            !.type = "CatchupPosition",
                            !.from = n,
                            !.to = election_leaderMember[n],
                            !.leadershipTermId = election_leadershipTermId[n],
                            !.logPosition = election_logPosition[n]])
          /\ election_state' = [election_state EXCEPT ![n] = "FOLLOWER_CATCHUP_AWAIT"]
          /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_logPosition, election_appendPosition,
                         election_logLeadershipTermId, election_leadershipTermId,
                         election_candidateTermId, election_notifiedCommitPosition,
                         election_leaderMember,
                         election_catchupJoinPosition,
                         election_replicationLeadershipTermId, election_replicationStopPosition,
                         election_replicationTermBaseLogPosition,
                         clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition>>
       \/ /\ Election_HandleError(n)
          /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, leaderMember, leadershipTermId,
                         notifiedCommitPosition, election_logLeadershipTermId, election_leadershipTermId, network>>

Election_FollowerCatchupAwait(n) ==
    /\ election_state[n] = "FOLLOWER_CATCHUP_AWAIT"
    /\ \/ /\ election_logSubscription[n].valid
          /\ election_logSubscription[n].position /= NullValue
          /\ election_logSubscription[n].position = election_logPosition[n]
          /\ election_state' = [election_state EXCEPT ![n] = "FOLLOWER_CATCHUP"]
          /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_logPosition, election_appendPosition,
                         election_logLeadershipTermId, election_leadershipTermId,
                         election_candidateTermId, election_notifiedCommitPosition,
                         election_leaderMember,
                         election_catchupJoinPosition, election_logSubscription,
                         election_replicationLeadershipTermId, election_replicationStopPosition,
                         election_replicationTermBaseLogPosition,
                         clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition, network>>
       \/ /\ ~election_logSubscription[n].valid \/ election_logSubscription[n].position = NullValue
          /\ Election_HandleError(n)
          /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, leaderMember, leadershipTermId,
                         notifiedCommitPosition, election_logLeadershipTermId, election_leadershipTermId, network>>

CM_UpdateFollowerPosition(n, leader) ==
    LET position == Len(log[n])
    IN /\ Send(network, [NullMsg EXCEPT
                         !.type = "AppendPosition",
                         !.from = n,
                         !.to = leader,
                         !.leadershipTermId = leadershipTermId[n],
                         !.logPosition = position])
       /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, logReplay, leadershipTermId,
                      logReplication, notifiedCommitPosition, election_state, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition, clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition>>

Election_FollowerCatchup(n) ==
    /\ election_state[n] = "FOLLOWER_CATCHUP"
    /\ \/ LET newPosition == election_logSubscription[n].position + 1
              remoteLogLength == Len(log[election_logSubscription[n].source])
              newEntry == IF remoteLogLength >= newPosition
                          THEN log[election_logSubscription[n].source][newPosition]
                          ELSE NullLogEntry
          IN /\ newEntry.type /= "Null"
             /\ newPosition < election_notifiedCommitPosition[n]
             /\ newPosition <= MaxLogLength \* STATE SPACE GUARD
             /\ election_logSubscription' = [election_logSubscription EXCEPT ![n].position = newPosition]
             /\ log' = [log EXCEPT ![n] = Append(@, newEntry)]
             /\ \/ /\ newEntry.type = "NewLeadershipTerm"
                   /\ CM_OnReplayNewLeadershipTermEvent(n, newEntry.leadershipTermId, newEntry.logPosition, newEntry.termBaseLogPosition)
                   /\ commitPosition' = [commitPosition EXCEPT ![n] = newPosition]
                   /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition,
                                  role, leaderMember, logReplay, logReplication,
                                  notifiedCommitPosition, election_state, election_appendPosition,
                                  election_leadershipTermId, election_candidateTermId,
                                  election_notifiedCommitPosition,
                                  election_leaderMember, election_catchupJoinPosition,
                                  election_replicationLeadershipTermId, election_replicationStopPosition,
                                  election_replicationTermBaseLogPosition,
                                  clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition, network>>
                \/ /\ newEntry.type /= "NewLeadershipTerm"
                   /\ commitPosition' = [commitPosition EXCEPT ![n] = newPosition]
                   /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, recordingLog,
                                  role, leaderMember, logReplay, leadershipTermId, logReplication,
                                  notifiedCommitPosition, election_state, election_logPosition,
                                  election_appendPosition, election_logLeadershipTermId,
                                  election_leadershipTermId, election_candidateTermId,
                                  election_notifiedCommitPosition,
                                  election_leaderMember, election_catchupJoinPosition,
                                  election_replicationLeadershipTermId, election_replicationStopPosition,
                                  election_replicationTermBaseLogPosition,
                                  clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition, network>>
       \/ CM_UpdateFollowerPosition(n, election_leaderMember[n])
       \/ /\ commitPosition[n] >= election_catchupJoinPosition[n]
          /\ commitPosition[n] >= election_notifiedCommitPosition[n]
          /\ election_appendPosition' = [election_appendPosition EXCEPT ![n] = commitPosition[n]]
          /\ election_logPosition' = [election_logPosition EXCEPT ![n] = commitPosition[n]]
          /\ election_state' = [election_state EXCEPT ![n] = "FOLLOWER_LOG_INIT"]
          /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_logLeadershipTermId,
                         election_leadershipTermId, election_candidateTermId,
                         election_notifiedCommitPosition,
                         election_leaderMember,
                         election_catchupJoinPosition,
                         election_logSubscription,
                         election_replicationLeadershipTermId, election_replicationStopPosition,
                         election_replicationTermBaseLogPosition,
                         clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition, network>>
       \/ /\ Election_HandleError(n)
          /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, leaderMember, leadershipTermId,
                         notifiedCommitPosition, election_logLeadershipTermId, election_leadershipTermId, network>>

Election_FollowerLogInit(n) ==
    /\ election_state[n] = "FOLLOWER_LOG_INIT"
    /\ \/ /\ ~election_logSubscription[n].valid
          /\ election_logSubscription' = [election_logSubscription EXCEPT ![n] = [ valid |-> TRUE, source |-> election_leaderMember[n], position |-> Len(log[n]) ] ]
          /\ election_state' = [election_state EXCEPT ![n] = "FOLLOWER_LOG_AWAIT"]
          /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, logReplay, leadershipTermId,
                         logReplication, notifiedCommitPosition,
                         election_logPosition, election_appendPosition,
                         election_logLeadershipTermId, election_leadershipTermId,
                         election_candidateTermId, election_notifiedCommitPosition,
                         election_leaderMember, election_catchupJoinPosition,
                         election_replicationLeadershipTermId, election_replicationStopPosition,
                         election_replicationTermBaseLogPosition,
                         clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition, network>>
       \/ /\ election_logSubscription[n].valid
          /\ election_state' = [election_state EXCEPT ![n] = "FOLLOWER_READY"]
          /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_logPosition, election_appendPosition,
                         election_logLeadershipTermId, election_leadershipTermId,
                         election_candidateTermId, election_notifiedCommitPosition,
                         election_leaderMember,
                         election_catchupJoinPosition, election_logSubscription,
                         election_replicationLeadershipTermId, election_replicationStopPosition,
                         election_replicationTermBaseLogPosition,
                         clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition, network>>

Election_FollowerLogAwait(n) ==
    /\ election_state[n] = "FOLLOWER_LOG_AWAIT"
    /\ \/ /\ RecordingLog_EnsureCoherent(n, election_leadershipTermId[n], election_logPosition[n], NullValue)
          /\ election_logLeadershipTermId' = [election_logLeadershipTermId EXCEPT ![n] = election_leadershipTermId[n]]
          /\ election_state' = [election_state EXCEPT ![n] = "FOLLOWER_READY"]
          /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log,
                         role, commitPosition, leaderMember, logReplay, leadershipTermId,
                         logReplication, notifiedCommitPosition,
                         election_logPosition, election_appendPosition,
                         election_leadershipTermId, election_candidateTermId,
                         election_notifiedCommitPosition,
                         election_leaderMember, election_catchupJoinPosition,
                         election_logSubscription,
                         election_replicationLeadershipTermId, election_replicationStopPosition,
                         election_replicationTermBaseLogPosition,
                         clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition, network>>
       \/ /\ Election_HandleError(n)
          /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, leaderMember, leadershipTermId,
                         notifiedCommitPosition, election_logLeadershipTermId, election_leadershipTermId, network>>

Election_FollowerReady(n) ==
    /\ election_state[n] = "FOLLOWER_READY"
    /\ \/ /\ Send(network, [NullMsg EXCEPT
                            !.type = "AppendPosition",
                            !.from = n,
                            !.to = election_leaderMember[n],
                            !.leadershipTermId = election_leadershipTermId[n],
                            !.logPosition = election_logPosition[n],
                            !.leaderMember = election_leaderMember[n]])
          /\ election_state' = [election_state EXCEPT ![n] = "CLOSED"]
          /\ CM_ElectionComplete(n)
          /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, election_logSubscription,
                         clusterMembers_candidateTermId, clusterMembers_leadershipTermId, clusterMembers_logPosition>>
       \/ /\ Election_HandleError(n)
          /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, leaderMember, leadershipTermId,
                         notifiedCommitPosition, election_logLeadershipTermId, election_leadershipTermId, network>>

CM_EnterElection(n, timeoutCount) ==
    /\ election_logPosition' = [election_logPosition EXCEPT ![n] = commitPosition[n]]
    /\ election_appendPosition' = [election_appendPosition EXCEPT ![n] = Len(log[n])]
    /\ election_logLeadershipTermId' = [election_logLeadershipTermId EXCEPT ![n] = leadershipTermId[n]]
    /\ election_leadershipTermId' = [election_leadershipTermId EXCEPT ![n] = leadershipTermId[n]]
    /\ election_candidateTermId' = [election_candidateTermId EXCEPT ![n] = Max2(nodeStateFile_candidateTermId[n], leadershipTermId[n])]
    /\ election_notifiedCommitPosition' = [election_candidateTermId EXCEPT ![n] = 0]
    /\ Election_State_CANVASS(n, timeoutCount)

\* @type: (Str, MSG) => Bool;
Election_OnAppendPosition(n, msg) ==
    \/ /\ msg.leadershipTermId <= election_leadershipTermId[n]
       /\ clusterMembers_logPosition' = [clusterMembers_logPosition EXCEPT ![n][msg.from] = msg.logPosition]
       /\ clusterMembers_leadershipTermId' = [clusterMembers_leadershipTermId EXCEPT ![n][msg.from] = msg.leadershipTermId]
       /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_state, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition, clusterMembers_vote,
                      clusterMembers_isBallotSent, clusterMembers_candidateTermId>>
    \/ /\ msg.leadershipTermId > election_leadershipTermId[n]
       /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_state, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition, clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition>>

\* @type: (Str, MSG, <<Str, Str>> -> MSG) => Bool;
CM_OnAppendPosition(n, msg, newNetwork) ==
    /\ msg.type = "AppendPosition"
    /\ msg.to = n
    /\ network' = newNetwork
    /\ \/ /\ election_state[n] /= "CLOSED"
          /\ Election_OnAppendPosition(n, msg)
       \/ /\ election_state[n] = "CLOSED"
          /\ msg.leadershipTermId > leadershipTermId[n]
          /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_state, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition, clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition>>
       \/ /\ election_state[n] = "CLOSED"
          /\ msg.leadershipTermId <= leadershipTermId[n]
          /\ role[n] = "LEADER"
          /\ clusterMembers_logPosition' = [clusterMembers_logPosition EXCEPT ![n][msg.from] = msg.logPosition]
          /\ clusterMembers_leadershipTermId' = [clusterMembers_leadershipTermId EXCEPT ![n][msg.from] = msg.leadershipTermId]
          /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_state, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition, clusterMembers_vote,
                         clusterMembers_isBallotSent, clusterMembers_candidateTermId>>
       \/ /\ election_state[n] = "CLOSED"
          /\ msg.leadershipTermId <= leadershipTermId[n]
          /\ role[n] /= "LEADER"
          /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_state, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition, clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition>>

\* @type: (Str, Str, Int, Int, <<Str, Str>> -> MSG) => Bool;
Election_PublishNewLeadershipTerm(n, destMember, logLeadershipTermId_param, quorumPosition, newNetwork) ==
    LET nextTermEntry == RecordingLog_FindTermEntry(n, logLeadershipTermId_param + 1) IN
    LET nextLeadershipTermId == IF nextTermEntry.valid THEN nextTermEntry.leadershipTermId ELSE election_leadershipTermId[n] IN
    LET nextTermBaseLogPosition == IF nextTermEntry.valid THEN nextTermEntry.termBaseLogPosition ELSE election_appendPosition[n] IN
    LET nextLogPosition == IF nextTermEntry.valid
                           THEN
                                IF nextTermEntry.logPosition /= NullValue
                                THEN nextTermEntry.logPosition
                                ELSE election_appendPosition[n]
                           ELSE NullValue IN
    Send(newNetwork, [NullMsg EXCEPT
                      !.type = "NewLeadershipTerm",
                      !.from = n,
                      !.to = destMember,
                      !.logLeadershipTermId = logLeadershipTermId_param,
                      !.nextLeadershipTermId = nextLeadershipTermId,
                      !.nextTermBaseLogPosition = nextTermBaseLogPosition,
                      !.nextLogPosition = nextLogPosition,
                      !.leadershipTermId = election_leadershipTermId[n],
                      !.termBaseLogPosition = election_appendPosition[n],
                      !.logPosition = election_appendPosition[n],
                      !.commitPosition = quorumPosition,
                      !.leaderMember = n])

\* @type: (Str, MSG, <<Str, Str>> -> MSG) => Bool;
Election_OnCanvassPosition(n, msg, newNetwork) ==
    /\ clusterMembers_logPosition' = [clusterMembers_logPosition EXCEPT ![n][msg.from] = msg.logPosition]
    /\ clusterMembers_leadershipTermId' = [clusterMembers_leadershipTermId EXCEPT ![n][msg.from] = msg.logLeadershipTermId]
    /\ \/ /\ msg.logLeadershipTermId < election_leadershipTermId[n]
          /\ role[n] = "LEADER"
          /\ Election_PublishNewLeadershipTerm(n, msg.from, msg.logLeadershipTermId, CM_QuorumPositionBoundedByLeaderLog1(n), newNetwork)
          /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_state, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition,
                         clusterMembers_vote, clusterMembers_isBallotSent, clusterMembers_candidateTermId>>
       \/ /\ msg.logLeadershipTermId > election_leadershipTermId[n]
          /\ election_state[n] \in {"LEADER_LOG_REPLICATION", "LEADER_READY"}
          /\ Election_HandleError(n)
          /\ network' = newNetwork
          /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, leaderMember, leadershipTermId,
                         notifiedCommitPosition, election_logLeadershipTermId, election_leadershipTermId>>
       \/ /\ \/ msg.logLeadershipTermId = election_leadershipTermId[n]
             \/ /\ msg.logLeadershipTermId < election_leadershipTermId[n]
                /\ role[n] /= "LEADER"
          /\ network' = newNetwork
          /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_state, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition, clusterMembers_vote,
                         clusterMembers_isBallotSent, clusterMembers_candidateTermId>>

\* @type: (Str, MSG, <<Str, Str>> -> MSG) => Bool;
CM_OnCanvassPosition(n, msg, newNetwork) ==
    /\ msg.type = "CanvassPosition"
    /\ msg.to = n
    /\ \/ /\ election_state[n] /= "CLOSED"
          /\ Election_OnCanvassPosition(n, msg, newNetwork)
       \/ /\ election_state[n] = "CLOSED"
          /\ \/ role[n] /= "LEADER"
             \/ /\ role[n] = "LEADER"
                /\ msg.logLeadershipTermId > leadershipTermId[n]
          /\ network' = newNetwork
          /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_state, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition, clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition>>
       \/ /\ election_state[n] = "CLOSED"
          /\ role[n] = "LEADER"
          /\ msg.logLeadershipTermId <= leadershipTermId[n]
          /\ clusterMembers_logPosition' = [clusterMembers_logPosition EXCEPT ![n][msg.from] = msg.logPosition]
          /\ clusterMembers_leadershipTermId' = [clusterMembers_leadershipTermId EXCEPT ![n][msg.from] = msg.logLeadershipTermId]
          /\ LET currentTermEntry == RecordingLog_FindTermEntry(n, leadershipTermId[n])
             IN \/ /\ ~currentTermEntry.valid
                   /\ network' = newNetwork
                   /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_state, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition, clusterMembers_vote,
                                  clusterMembers_isBallotSent, clusterMembers_candidateTermId>>
                \/ /\ currentTermEntry.valid
                   /\ \/ /\ msg.logLeadershipTermId < leadershipTermId[n]
                         /\ LET nextLogEntry == RecordingLog_FindTermEntry(n, msg.logLeadershipTermId + 1)
                                nextLogLeadershipTermId == IF nextLogEntry.valid THEN nextLogEntry.leadershipTermId
                                                           ELSE leadershipTermId[n]
                                nextTermBaseLogPosition == IF nextLogEntry.valid THEN nextLogEntry.termBaseLogPosition
                                                           ELSE currentTermEntry.termBaseLogPosition
                                nextLogPosition_val == IF nextLogEntry.valid THEN nextLogEntry.logPosition
                                                   ELSE NullValue
                            IN /\ Send(newNetwork, [NullMsg EXCEPT
                                                    !.type = "NewLeadershipTerm",
                                                    !.from = n,
                                                    !.to = msg.from,
                                                    !.logLeadershipTermId = msg.logLeadershipTermId,
                                                    !.nextLeadershipTermId = nextLogLeadershipTermId,
                                                    !.nextTermBaseLogPosition = nextTermBaseLogPosition,
                                                    !.nextLogPosition = nextLogPosition_val,
                                                    !.leadershipTermId = leadershipTermId[n],
                                                    !.termBaseLogPosition = currentTermEntry.termBaseLogPosition,
                                                    !.logPosition = Len(log[n]),
                                                    !.commitPosition = commitPosition[n],
                                                    !.leaderMember = n ])
                               /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_state, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition,
                                              clusterMembers_vote, clusterMembers_isBallotSent,
                                              clusterMembers_candidateTermId>>
                      \/ /\ Send(newNetwork, [NullMsg EXCEPT
                                              !.type = "NewLeadershipTerm",
                                              !.from = n,
                                              !.to = msg.from,
                                              !.logLeadershipTermId = msg.logLeadershipTermId,
                                              !.nextLeadershipTermId = NullValue,
                                              !.nextTermBaseLogPosition = NullValue,
                                              !.nextLogPosition = NullValue,
                                              !.leadershipTermId = leadershipTermId[n],
                                              !.termBaseLogPosition = currentTermEntry.termBaseLogPosition,
                                              !.logPosition = Len(log[n]),
                                              !.commitPosition = commitPosition[n],
                                              !.leaderMember = n ])
                         /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_state, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition,
                                        clusterMembers_vote, clusterMembers_isBallotSent,
                                        clusterMembers_candidateTermId>>

\* @type: (Str, MSG, <<Str, Str>> -> MSG) => Bool;
CM_OnCatchupPosition(n, msg, newNetwork) ==
    /\ msg.type = "CatchupPosition"
    /\ msg.to = n
    /\ \/ /\ \/ role[n] /= "LEADER"
             \/ /\ role[n] = "LEADER"
                /\ msg.leadershipTermId > leadershipTermId[n]
          /\ network' = newNetwork
          /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_state, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition, clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition>>
       \/ /\ role[n] = "LEADER"
          /\ msg.leadershipTermId <= leadershipTermId[n]
          /\ election_logSubscription' = [election_logSubscription EXCEPT ![msg.from] = [ valid |-> TRUE, source |-> n, position |-> msg.logPosition ] ]
          /\ network' = newNetwork
          /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, logReplay, leadershipTermId,
                         logReplication, notifiedCommitPosition, election_state,
                         election_logPosition, election_appendPosition,
                         election_logLeadershipTermId, election_leadershipTermId,
                         election_candidateTermId, election_notifiedCommitPosition,
                         election_leaderMember,
                         election_catchupJoinPosition,
                         election_replicationLeadershipTermId, election_replicationStopPosition,
                         election_replicationTermBaseLogPosition,
                         clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition>>

\* @type: (Str, MSG) => Bool;
Election_OnCommitPosition(n, msg) ==
    \/ /\ msg.from = election_leaderMember[n]
       /\ election_notifiedCommitPosition' = [election_notifiedCommitPosition EXCEPT ![n] = msg.logPosition]
       /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_state, election_logPosition, election_appendPosition,
                      election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId,
                      election_leaderMember,
                      election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId,
                      election_replicationStopPosition, election_replicationTermBaseLogPosition,
                      clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition>>
    \/ /\ msg.from /= election_leaderMember[n]
       /\ \/ /\ msg.leadershipTermId <= election_leadershipTermId[n]
             /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_state, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition, clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition>>
          \/ /\ msg.leadershipTermId > election_leadershipTermId[n]
             /\ election_state[n] = "LEADER_READY"
             /\ Election_HandleError(n)
             /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, leaderMember, leadershipTermId,
                            notifiedCommitPosition, election_logLeadershipTermId, election_leadershipTermId>>

\* @type: (Str, MSG, <<Str, Str>> -> MSG) => Bool;
CM_OnCommitPosition(n, msg, newNetwork) ==
    /\ msg.type = "CommitPosition"
    /\ msg.to = n
    /\ network' = newNetwork
    /\ \/ /\ election_state[n] /= "CLOSED"
          /\ Election_OnCommitPosition(n, msg)
       \/ /\ election_state[n] = "CLOSED"
          /\ \/ /\ msg.leadershipTermId = leadershipTermId[n]
                /\ \/ /\ msg.from = leaderMember[n]
                      /\ role[n] = "FOLLOWER"
                      /\ notifiedCommitPosition' = [notifiedCommitPosition EXCEPT ![n] = msg.logPosition]
                      /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, logReplay,
                                     leadershipTermId, logReplication,
                                     election_state, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition, clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition>>
                   \/ /\ \/ msg.from /= leaderMember[n]
                         \/ role[n] /= "FOLLOWER"
                      /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_state, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition, clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition>>
             \/ /\ msg.leadershipTermId < leadershipTermId[n]
                /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_state, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition, clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition>>
             \/ /\ msg.leadershipTermId > leadershipTermId[n]
                /\ CM_EnterElection(n, 0)
                /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, notifiedCommitPosition, leaderMember, commitPosition,
                               leadershipTermId>>

\* @type: (Str, MSG) => Bool;
Election_OnNewLeadershipTerm(n, msg) ==
    /\ \/ /\ \/ election_state[n] = "FOLLOWER_BALLOT"
             \/ election_state[n] = "CANDIDATE_BALLOT"
          /\ msg.leadershipTermId = election_candidateTermId[n]
       \/ election_state[n] = "CANVASS"
    /\ \/ /\ msg.logLeadershipTermId /= election_logLeadershipTermId[n]
          /\ Election_State_CANVASS(n, 0)
          /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition,
                         election_logPosition, election_appendPosition, election_logLeadershipTermId,
                         election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition>>
       \/ /\ msg.logLeadershipTermId = election_logLeadershipTermId[n]
          /\ \/ /\ msg.nextTermBaseLogPosition /= NullValue
                /\ msg.nextTermBaseLogPosition < election_appendPosition[n]
                /\ Len(log[n]) >= msg.nextTermBaseLogPosition
                /\ Len(log[n]) >= 1
                /\ log' = [log EXCEPT ![n] = SubSeq(log[n], 1, msg.nextTermBaseLogPosition)]
                /\ election_appendPosition' = [election_appendPosition EXCEPT ![n] = msg.nextTermBaseLogPosition]
                \* Replaces CHOOSE-based recording log update with function comprehension
                /\ LET matchTermId == msg.logLeadershipTermId
                   IN recordingLog' = [recordingLog EXCEPT ![n] =
                       [i \in 0..MaxLeadershipTerm |->
                           IF recordingLog[n][i].valid /\ recordingLog[n][i].leadershipTermId = matchTermId
                           THEN [recordingLog[n][i] EXCEPT !.logPosition = msg.nextTermBaseLogPosition]
                           ELSE recordingLog[n][i]
                       ]]
                /\ Election_HandleError(n)
                /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, leaderMember, leadershipTermId,
                               notifiedCommitPosition, election_logLeadershipTermId, election_leadershipTermId>>
             \/ /\ \/ msg.nextTermBaseLogPosition = NullValue
                   \/ msg.nextTermBaseLogPosition >= election_appendPosition[n]
                /\ election_leadershipTermId' = [election_leadershipTermId EXCEPT ![n] = msg.leadershipTermId]
                /\ \/ /\ election_appendPosition[n] >= msg.termBaseLogPosition
                      /\ election_catchupJoinPosition' = [election_catchupJoinPosition EXCEPT ![n] = IF election_appendPosition[n] < msg.logPosition THEN msg.logPosition ELSE NullValue]
                      /\ Election_State_FOLLOWER_REPLAY(n)
                      /\ election_leaderMember' = [election_leaderMember EXCEPT ![n] = msg.leaderMember]
                      /\ election_candidateTermId' = [election_candidateTermId EXCEPT ![n] = Max2(election_candidateTermId[n], msg.leadershipTermId)]
                      /\ election_notifiedCommitPosition' = [election_notifiedCommitPosition EXCEPT ![n] = Max2(election_notifiedCommitPosition[n], msg.commitPosition)]
                      /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, commitPosition, leaderMember, logReplay,
                                     leadershipTermId, logReplication,
                                     notifiedCommitPosition, election_logPosition, election_appendPosition,
                                     election_logLeadershipTermId, election_logSubscription,
                                     election_replicationLeadershipTermId, election_replicationStopPosition,
                                     election_replicationTermBaseLogPosition, clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition>>
                   \/ /\ election_appendPosition[n] < msg.termBaseLogPosition
                      /\ \/ /\ msg.nextLeadershipTermId = NullValue
                            /\ Election_HandleError(n)
                            /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, leaderMember, leadershipTermId,
                                           notifiedCommitPosition, election_logLeadershipTermId>>
                         \/ /\ msg.nextLeadershipTermId /= NullValue
                            /\ election_catchupJoinPosition' = [election_catchupJoinPosition EXCEPT ![n] = IF election_appendPosition[n] < msg.logPosition THEN msg.logPosition ELSE NullValue]
                            /\ election_leaderMember' = [election_leaderMember EXCEPT ![n] = msg.leaderMember]
                            /\ election_candidateTermId' = [election_candidateTermId EXCEPT ![n] = Max2(election_candidateTermId[n], msg.leadershipTermId)]
                            /\ election_notifiedCommitPosition' = [election_notifiedCommitPosition EXCEPT ![n] = Max2(election_notifiedCommitPosition[n], msg.commitPosition)]
                            /\ \/ /\ election_appendPosition[n] < msg.nextTermBaseLogPosition
                                  /\ election_replicationLeadershipTermId' = [election_replicationLeadershipTermId EXCEPT ![n] = msg.logLeadershipTermId]
                                  /\ election_replicationStopPosition' = [election_replicationStopPosition EXCEPT ![n] = msg.nextTermBaseLogPosition]
                                  /\ election_replicationTermBaseLogPosition' = [election_replicationTermBaseLogPosition EXCEPT ![n] = NullValue]
                                  /\ Election_State_FOLLOWER_LOG_REPLICATION(n)
                                  /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, commitPosition, leaderMember, logReplay,
                                                 leadershipTermId, logReplication,
                                                 notifiedCommitPosition, election_logPosition, election_appendPosition,
                                                 election_logLeadershipTermId, election_logSubscription,
                                                 clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition>>
                               \/ /\ election_appendPosition[n] = msg.nextTermBaseLogPosition
                                  /\ msg.nextLogPosition /= NullValue
                                  /\ election_replicationLeadershipTermId' = [election_replicationLeadershipTermId EXCEPT ![n] = msg.nextLeadershipTermId]
                                  /\ election_replicationStopPosition' = [election_replicationStopPosition EXCEPT ![n] = msg.nextLogPosition]
                                  /\ election_replicationTermBaseLogPosition' = [election_replicationTermBaseLogPosition EXCEPT ![n] = msg.nextTermBaseLogPosition]
                                  /\ Election_State_FOLLOWER_LOG_REPLICATION(n)
                                  /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, commitPosition, leaderMember, logReplay,
                                                 leadershipTermId, logReplication,
                                                 notifiedCommitPosition, election_logPosition, election_appendPosition,
                                                 election_logLeadershipTermId, election_logSubscription,
                                                 clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition>>
                               \/ /\ \/ election_appendPosition[n] > msg.nextTermBaseLogPosition
                                     \/ /\ election_appendPosition[n] = msg.nextTermBaseLogPosition
                                        /\ msg.nextLogPosition = NullValue
                                  /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, logReplay,
                                                 leadershipTermId, logReplication,
                                                 notifiedCommitPosition, election_state, election_logPosition,
                                                 election_appendPosition, election_logLeadershipTermId,
                                                 election_logSubscription, election_replicationLeadershipTermId,
                                                 election_replicationStopPosition, election_replicationTermBaseLogPosition,
                                                 clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition>>

\* @type: (Str, MSG, <<Str, Str>> -> MSG) => Bool;
CM_OnNewLeadershipTerm(n, msg, newNetwork) ==
    /\ msg.type = "NewLeadershipTerm"
    /\ msg.to = n
    /\ network' = newNetwork
    /\ \/ /\ election_state[n] /= "CLOSED"
          /\ Election_OnNewLeadershipTerm(n, msg)
       \/ /\ election_state[n] = "CLOSED"
          /\ \/ /\ role[n] = "FOLLOWER"
                /\ msg.leadershipTermId = leadershipTermId[n]
                /\ msg.leaderMember = leaderMember[n]
                /\ notifiedCommitPosition' = [notifiedCommitPosition EXCEPT ![n] = Max2(msg.commitPosition, notifiedCommitPosition[n])]
                /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, logReplay, leadershipTermId,
                               logReplication, election_state, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition, clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition>>
             \/ /\ msg.leadershipTermId > leadershipTermId[n]
                /\ CM_EnterElection(n, 0)
                /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, notifiedCommitPosition, leaderMember, commitPosition,
                               leadershipTermId>>
             \/ /\ \/ /\ msg.leadershipTermId = leadershipTermId[n]
                      /\ \/ msg.leaderMember /= leaderMember[n]
                         \/ role[n] /= "FOLLOWER"
                   \/ msg.leadershipTermId < leadershipTermId[n]
                /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_state, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition, clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition>>

\* @type: (Str, Str, Int, Int, <<Str, Str>> -> MSG) => Bool;
Election_PlaceVote(n, candidate, candidateTermId_param, vote, newNetwork) ==
    Send(newNetwork, [NullMsg EXCEPT
                      !.type = "Vote",
                      !.from = n,
                      !.to = candidate,
                      !.candidateTermId = candidateTermId_param,
                      !.logLeadershipTermId = election_logLeadershipTermId[n],
                      !.logPosition = election_appendPosition[n],
                      !.vote = vote])

\* @type: (Str, MSG, <<Str, Str>> -> MSG) => Bool;
Election_OnRequestVote(n, msg, newNetwork) ==
    \/ /\ msg.candidateTermId <= election_candidateTermId[n]
       /\ Election_PlaceVote(n, msg.from, msg.candidateTermId, VoteFalse, newNetwork)
       /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_state, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition, clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition>>
    \/ /\ msg.candidateTermId > election_candidateTermId[n]
       /\ ClusterMember_CompareLog0(election_logLeadershipTermId[n], election_appendPosition[n], msg.logLeadershipTermId, msg.logPosition) > 0
       /\ LET newCandidateTermId == Max2(nodeStateFile_candidateTermId[n], msg.candidateTermId)
          IN /\ NodeStateFile_ProposeMaxCandidateTermId(n, newCandidateTermId, msg.logPosition)
             /\ Election_PlaceVote(n, msg.from, msg.candidateTermId, VoteFalse, newNetwork)
             /\ \/ /\ role[n] = "LEADER"
                   /\ Election_PublishNewLeadershipTerm(n, msg.from, msg.logLeadershipTermId, CM_QuorumPositionBoundedByLeaderLog1(n), newNetwork)
                   /\ UNCHANGED <<log, recordingLog, role, commitPosition, leaderMember, logReplay,
                                  leadershipTermId, logReplication, notifiedCommitPosition,
                                  election_state, election_logPosition, election_appendPosition,
                                  election_logLeadershipTermId, election_leadershipTermId, election_notifiedCommitPosition,
                                  election_leaderMember, election_catchupJoinPosition,
                                  election_logSubscription, election_replicationLeadershipTermId,
                                  election_replicationStopPosition, election_replicationTermBaseLogPosition,
                                  clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition>>
                \/ /\ role[n] /= "LEADER"
                   /\ UNCHANGED <<log, recordingLog, role, commitPosition, leaderMember, logReplay,
                                  leadershipTermId, logReplication, notifiedCommitPosition,
                                  election_state, election_logPosition, election_appendPosition,
                                  election_logLeadershipTermId, election_leadershipTermId, election_notifiedCommitPosition,
                                  election_leaderMember, election_catchupJoinPosition,
                                  election_logSubscription, election_replicationLeadershipTermId,
                                  election_replicationStopPosition, election_replicationTermBaseLogPosition,
                                  clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition>>
    \/ /\ msg.candidateTermId > election_candidateTermId[n]
       /\ ClusterMember_CompareLog0(election_logLeadershipTermId[n], election_appendPosition[n], msg.logLeadershipTermId, msg.logPosition) <= 0
       /\ \/ /\ election_state[n] \in {"CANVASS", "NOMINATE", "CANDIDATE_BALLOT", "FOLLOWER_BALLOT"}
             /\ NodeStateFile_ProposeMaxCandidateTermId(n, msg.candidateTermId, msg.logPosition)
             /\ Election_PlaceVote(n, msg.from, msg.candidateTermId, VoteTrue, newNetwork)
             /\ election_state' = [election_state EXCEPT ![n] = "FOLLOWER_BALLOT"]
             /\ UNCHANGED <<log, recordingLog, role, commitPosition, leaderMember, logReplay,
                            leadershipTermId, logReplication, notifiedCommitPosition,
                            election_logPosition, election_appendPosition,
                            election_logLeadershipTermId, election_leadershipTermId, election_notifiedCommitPosition,
                            election_leaderMember, election_catchupJoinPosition,
                            election_logSubscription, election_replicationLeadershipTermId,
                            election_replicationStopPosition, election_replicationTermBaseLogPosition,
                            clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition>>
          \/ /\ election_state[n] \notin {"CANVASS", "NOMINATE", "CANDIDATE_BALLOT", "FOLLOWER_BALLOT"}
             /\ network' = newNetwork
             /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_state, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition, clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition>>

\* @type: (Str, MSG, <<Str, Str>> -> MSG) => Bool;
CM_OnRequestVote(n, msg, newNetwork) ==
    /\ msg.type = "RequestVote"
    /\ msg.to = n
    /\ \/ /\ election_state[n] /= "CLOSED"
          /\ Election_OnRequestVote(n, msg, newNetwork)
       \/ /\ election_state[n] = "CLOSED"
          /\ msg.candidateTermId > leadershipTermId[n]
          /\ network' = newNetwork
          /\ CM_EnterElection(n, 0)
          /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, notifiedCommitPosition, leaderMember, commitPosition, leadershipTermId>>
       \/ /\ election_state[n] = "CLOSED"
          /\ msg.candidateTermId <= leadershipTermId[n]
          /\ network' = newNetwork
          /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_state, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition, clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition>>

\* @type: (Str, MSG) => Bool;
Election_OnVote(n, msg) ==
    \/ /\ election_state[n] = "CANDIDATE_BALLOT"
       /\ msg.candidateTermId = election_candidateTermId[n]
       /\ clusterMembers_candidateTermId' = [clusterMembers_candidateTermId EXCEPT ![n][msg.from] = msg.candidateTermId]
       /\ clusterMembers_vote' = [clusterMembers_vote EXCEPT ![n][msg.from] = msg.vote]
       /\ clusterMembers_leadershipTermId' = [clusterMembers_leadershipTermId EXCEPT ![n][msg.from] = msg.logLeadershipTermId]
       /\ clusterMembers_logPosition' = [clusterMembers_logPosition EXCEPT ![n][msg.from] = msg.logPosition]
       /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_state, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition, clusterMembers_isBallotSent>>
    \/ /\ \/ election_state[n] /= "CANDIDATE_BALLOT"
          \/ msg.candidateTermId /= election_candidateTermId[n]
       /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_state, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition, clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition>>

\* @type: (Str, MSG, <<Str, Str>> -> MSG) => Bool;
CM_OnVote(n, msg, newNetwork) ==
    /\ msg.type = "Vote"
    /\ msg.to = n
    /\ network' = newNetwork
    /\ \/ /\ election_state[n] /= "CLOSED"
          /\ Election_OnVote(n, msg)
       \/ /\ election_state[n] = "CLOSED"
          /\ UNCHANGED<<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_state, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition, clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition>>

CM_AppendMsg(n) ==
    /\ Len(log[n]) < MaxLogLength \* STATE SPACE GUARD
    /\ \E value \in Payloads :
            LET msg == [type |-> "SessionMessage", payload |-> value,
                        leadershipTermId |-> NullValue, logPosition |-> NullValue,
                        leaderMember |-> Null, termBaseLogPosition |-> NullValue]
            IN /\ log' = [log EXCEPT ![n] = Append(@, msg)]
               /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, recordingLog, role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication,
                              election_state, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition, clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition, network>>

CM_ConsensusWork(n) ==
    /\ election_state[n] = "CLOSED"
    /\ \/ /\ role[n] = "LEADER"
          /\ CM_AppendMsg(n)
       \/ /\ role[n] = "LEADER"
          /\ LET appendPos == Len(log[n])
                 quorumPos == CM_QuorumPositionBoundedByLeaderLog0(n, appendPos)
             IN CM_UpdateLeaderPosition(n, appendPos, quorumPos)
       \/ \* This is a deviation from the Java implementation, to allow multi-election testing with only 2 nodes,
          \* by entering an election arbitrarily on the leader node too.
          /\ CM_EnterElection(n, 1)
          /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog, notifiedCommitPosition, leaderMember, commitPosition, leadershipTermId,
                         network>>
       \/ /\ role[n] = "FOLLOWER"
          /\ election_logSubscription[n].valid
          /\ election_logSubscription[n].position /= NullValue
          /\ LET newPosition == election_logSubscription[n].position + 1
                 logEntry == IF Len(log[leaderMember[n]]) >= newPosition THEN log[leaderMember[n]][newPosition] ELSE NullLogEntry
             IN /\ logEntry.type /= "Null"
                /\ newPosition <= MaxLogLength \* STATE SPACE GUARD
                /\ log' = [log EXCEPT ![n] = Append(@, logEntry)]
                /\ election_logSubscription' = [election_logSubscription EXCEPT ![n].position = newPosition]
                /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, recordingLog,
                               role, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition, logReplay, logReplication, election_state, election_logPosition,
                               election_appendPosition, election_logLeadershipTermId, election_leadershipTermId,
                               election_candidateTermId,
                               election_notifiedCommitPosition, election_leaderMember,
                               election_catchupJoinPosition,
                               election_replicationLeadershipTermId, election_replicationStopPosition,
                               election_replicationTermBaseLogPosition, clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition, network>>
       \/ /\ role[n] = "FOLLOWER"
          /\ CM_UpdateFollowerPosition(n, leaderMember[n])
       \/ /\ role[n] = "FOLLOWER"
          /\ notifiedCommitPosition[n] > commitPosition[n]
          /\ Len(log[n]) > commitPosition[n]
          /\ commitPosition' = [commitPosition EXCEPT ![n] = commitPosition[n] + 1]
          /\ LET logEntry == log[n][commitPosition[n] + 1] IN
                /\ \/ /\ logEntry.type = "NewLeadershipTerm"
                      /\ CM_OnReplayNewLeadershipTermEvent(n, logEntry.leadershipTermId, logEntry.logPosition, logEntry.termBaseLogPosition)
                      /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, role, leaderMember,
                                     logReplay, logReplication,
                                     notifiedCommitPosition, election_state,
                                     election_appendPosition, election_leadershipTermId, election_candidateTermId,
                                     election_notifiedCommitPosition, election_leaderMember,
                                     election_catchupJoinPosition, election_logSubscription,
                                     election_replicationLeadershipTermId, election_replicationStopPosition,
                                     election_replicationTermBaseLogPosition, clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition, network>>
                   \/ /\ logEntry.type /= "NewLeadershipTerm"
                      /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog,
                                     role, leaderMember, logReplay, leadershipTermId, logReplication,
                                     notifiedCommitPosition, election_state, election_logPosition, election_appendPosition, election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, election_leaderMember, election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId, election_replicationStopPosition, election_replicationTermBaseLogPosition,
                                     clusterMembers_vote, clusterMembers_candidateTermId, clusterMembers_isBallotSent, clusterMembers_leadershipTermId, clusterMembers_logPosition, network>>

Adapter_OnAppendPosition(src, dest) ==
    /\ HasMessage(src, dest, "AppendPosition")
    /\ CM_OnAppendPosition(dest, network[src, dest], ConsumeMessage(src, dest))

Adapter_OnCanvassPosition(src, dest) ==
    /\ HasMessage(src, dest, "CanvassPosition")
    /\ CM_OnCanvassPosition(dest, network[src, dest], ConsumeMessage(src, dest))

Adapter_OnCatchupPosition(src, dest) ==
    /\ HasMessage(src, dest, "CatchupPosition")
    /\ CM_OnCatchupPosition(dest, network[src, dest], ConsumeMessage(src, dest))

Adapter_OnCommitPosition(src, dest) ==
    /\ HasMessage(src, dest, "CommitPosition")
    /\ CM_OnCommitPosition(dest, network[src, dest], ConsumeMessage(src, dest))

Adapter_OnNewLeadershipTerm(src, dest) ==
    /\ HasMessage(src, dest, "NewLeadershipTerm")
    /\ CM_OnNewLeadershipTerm(dest, network[src, dest], ConsumeMessage(src, dest))

Adapter_OnRequestVote(src, dest) ==
    /\ HasMessage(src, dest, "RequestVote")
    /\ CM_OnRequestVote(dest, network[src, dest], ConsumeMessage(src, dest))

Adapter_OnVote(src, dest) ==
    /\ HasMessage(src, dest, "Vote")
    /\ CM_OnVote(dest, network[src, dest], ConsumeMessage(src, dest))

\* Internal next-state relation (does not assign checker_timeoutCount)
InternalNext ==
    \/ \E n \in Nodes :
        \/ Election_Canvass(n)
        \/ Election_Nominate(n)
        \/ Election_CandidateBallot(n)
        \/ Election_FollowerBallot(n)
        \/ Election_LeaderLogReplication(n)
        \/ Election_LeaderReplay(n)
        \/ Election_LeaderInit(n)
        \/ Election_LeaderReady(n)
        \/ Election_FollowerLogReplication(n)
        \/ Election_FollowerReplay(n)
        \/ Election_FollowerCatchupInit(n)
        \/ Election_FollowerCatchupAwait(n)
        \/ Election_FollowerCatchup(n)
        \/ Election_FollowerLogInit(n)
        \/ Election_FollowerLogAwait(n)
        \/ Election_FollowerReady(n)
        \/ CM_ConsensusWork(n)

        \/ \E src \in Nodes \ {n}:
            \/ Adapter_OnAppendPosition(src, n)
            \/ Adapter_OnCanvassPosition(src, n)
            \/ Adapter_OnCatchupPosition(src, n)
            \/ Adapter_OnCommitPosition(src, n)
            \/ Adapter_OnNewLeadershipTerm(src, n)
            \/ Adapter_OnRequestVote(src, n)
            \/ Adapter_OnVote(src, n)

\* checker_timeoutCount is not used in the Apalache version — Apalache's --length
\* parameter serves the same state-space bounding purpose.
Next == InternalNext

Spec == Init /\ [][Next]_vars

\* Type invariant to catch basic errors
TypeInvariant ==
    /\ \A n \in Nodes : role[n] \in Roles
    /\ \A n \in Nodes : election_state[n] \in ElectionState
    /\ \A n \in Nodes : leaderMember[n] \in OptionalNode
    /\ \A n \in Nodes : commitPosition[n] \in Nat
    /\ \A n \in Nodes : leadershipTermId[n] \in Int
    /\ \A n \in Nodes : election_candidateTermId[n] \in Int
    /\ \A n \in Nodes : nodeStateFile_candidateTermId[n] \in Int
    /\ \A n, m \in Nodes : network[n, m].type \in MessageTypes \cup {"Null"}

\* Invariant for debugging that will be falsified when replication works to some extent.
HasReplicated ==
    /\ \A n \in Nodes: commitPosition[n] > 0
    /\ \A n1, n2 \in Nodes:
        LET minCommitPos == Min2(commitPosition[n1], commitPosition[n2]) IN
        SubSeq(log[n1], 1, minCommitPos) = SubSeq(log[n2], 1, minCommitPos)

Debug_Replication == ~HasReplicated

Debug_CompleteElection ==
    ~ /\ HasReplicated
      /\ \A n \in Nodes : election_state[n] = "CLOSED"

Debug_StartAnotherElection ==
    ~ /\ HasReplicated
      /\ Cardinality({n \in Nodes : /\ election_state[n] /= "CLOSED"
                                    /\ election_leaderMember[n] = Null}) >= QuorumSize

Debug_AnotherCandidate ==
    ~ /\ HasReplicated
      /\ \E n \in Nodes : role[n] = "CANDIDATE"

Debug_AnotherLeader ==
    ~ /\ HasReplicated
      /\ Cardinality({n \in Nodes : role[n] = "LEADER"}) >= 2

\* Invariant for debugging that will be falsified when multiple elections have completed on all nodes.
\* (SelectSeq replaced with Cardinality over DOMAIN)
Debug_CompleteMultipleElections ==
    ~ \E n \in Nodes :
                       /\ commitPosition[n] >= 2
                       /\ leadershipTermId[n] >= 1
                       /\ Cardinality({ i \in DOMAIN log[n] : log[n][i].type = "NewLeadershipTerm" }) >= 2

=============================================================================

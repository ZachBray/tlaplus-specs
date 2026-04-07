-------------------------- MODULE AeronRaft --------------------------
EXTENDS Naturals, Integers, FiniteSets, Sequences, SequencesExt, TLC

\* Based on Aeron commit 717903af0087e2c488f292e3577fb44ec1d52a01.

CONSTANT Nodes
CONSTANT ArbitraryFirstLeader
CONSTANT Payloads
CONSTANT Null

VARIABLE nodeStateFile_candidateTermId
VARIABLE nodeStateFile_logPosition
VARIABLE log
VARIABLE recordingLog
VARIABLE role
VARIABLE commitPosition
VARIABLE leaderMember
VARIABLE logReplay
VARIABLE leadershipTermId
VARIABLE logReplication
VARIABLE notifiedCommitPosition
VARIABLE election_replicationLeadershipTermId
VARIABLE election_replicationStopPosition
VARIABLE election_replicationTermBaseLogPosition
VARIABLE election_state
VARIABLE election_logPosition
VARIABLE election_appendPosition
VARIABLE election_logLeadershipTermId
VARIABLE election_leadershipTermId
VARIABLE election_candidateTermId
VARIABLE election_notifiedCommitPosition
VARIABLE election_leaderMember
VARIABLE election_catchupJoinPosition
VARIABLE election_logSubscription
VARIABLE clusterMembers_isBallotSent
VARIABLE clusterMembers_vote
VARIABLE clusterMembers_candidateTermId
VARIABLE clusterMembers_leadershipTermId
VARIABLE clusterMembers_logPosition
VARIABLE network

\* Variables for limiting the state space search, rather than modelling the actual behaviour.
VARIABLE checker_timeoutCount

MaxLeadershipTerm == 2
MaxTimeoutCount == Cardinality(Nodes) * 2
MaxLogLength == 4
ArbitraryFirstLeader == CHOOSE n \in Nodes : TRUE

Symmetry == { p[1] @@ p[2] : p \in Permutations(Nodes \ {ArbitraryFirstLeader}) \X Permutations(Payloads) }

NodeCount == Cardinality(Nodes)

Roles == {
    "LEADER",
    "FOLLOWER",
    "CANDIDATE"
}

ElectionState == {
    \* "INIT" is collapsed into "CANVASS" to help minimise the state space.
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

EmptyFunction == [x \in {} |-> x]

Init ==
    /\ network = [src \in Nodes, dest \in Nodes |-> Null]
    /\ nodeStateFile_candidateTermId = [n \in Nodes |-> NullValue]
    /\ nodeStateFile_logPosition = [n \in Nodes |-> NullValue]
    /\ log = [n \in Nodes |-> << >>]
    /\ recordingLog = [n \in Nodes |-> EmptyFunction]
    /\ role = [n \in Nodes |-> "FOLLOWER"]
    /\ commitPosition = [n \in Nodes |-> 0]
    /\ leaderMember = [n \in Nodes |-> Null]
    /\ logReplay = [n \in Nodes |-> Null]
    /\ leadershipTermId = [n \in Nodes |-> NullValue]
    /\ logReplication = [n \in Nodes |-> Null]
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
    /\ election_logSubscription = [n \in Nodes |-> Null]
    /\ election_replicationLeadershipTermId = [n \in Nodes |-> NullValue]
    /\ election_replicationStopPosition = [n \in Nodes |-> NullValue]
    /\ election_replicationTermBaseLogPosition = [n \in Nodes |-> NullValue]
    /\ clusterMembers_vote = [n \in Nodes |-> [m \in Nodes |-> Null]]
    /\ clusterMembers_candidateTermId = [n \in Nodes |-> [m \in Nodes |-> NullValue]]
    /\ clusterMembers_isBallotSent = [n \in Nodes |-> [m \in Nodes |-> FALSE]]
    /\ clusterMembers_leadershipTermId = [n \in Nodes |-> [m \in Nodes |-> NullValue]]
    /\ clusterMembers_logPosition = [n \in Nodes |-> [m \in Nodes |-> IF m = n THEN 0 ELSE NullValue]]
    /\ checker_timeoutCount = 0

persistent_state == <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log, recordingLog>>

non_replication_module_fields == <<role, commitPosition, leaderMember, leadershipTermId,
                                   notifiedCommitPosition>>

module_fields == <<non_replication_module_fields, logReplay, logReplication>>

election_fields == <<election_logPosition, election_appendPosition,
                     election_logLeadershipTermId, election_leadershipTermId,
                     election_candidateTermId, election_notifiedCommitPosition,
                     election_leaderMember,
                     election_catchupJoinPosition, election_logSubscription,
                     election_replicationLeadershipTermId, election_replicationStopPosition,
                     election_replicationTermBaseLogPosition>>

member_fields == <<clusterMembers_vote, clusterMembers_candidateTermId,
                   clusterMembers_isBallotSent, clusterMembers_leadershipTermId,
                   clusterMembers_logPosition>>


checker_vars == <<checker_timeoutCount>>

vars == <<persistent_state, module_fields, election_state, election_fields, member_fields, network, checker_vars>>

\*Max(S) == CHOOSE x \in S : \A y \in S : x >= y
\*
\*Min(S) == CHOOSE x \in S : \A y \in S : x <= y

\* Send with unicast-style backpressure
Send(newNetwork, msg) ==
    /\ newNetwork[msg.from, msg.to] = Null
    /\ network' = [newNetwork EXCEPT ![msg.from, msg.to] = msg]

\* Send with mc-max-fc-style backpressure
Broadcast(newNetwork, msg) ==
    LET destinations == { d \in Nodes : d /= msg.from /\ newNetwork[msg.from, d] = Null }
    IN /\ destinations /= {}
       /\ network' = [<<from, to>> \in {msg.from} \X destinations |-> [to |-> to] @@ msg] @@ newNetwork

HasMessage(src, dest, type) ==
    LET msg == network[src, dest] IN
    /\ msg /= Null
    /\ msg.type = type

ConsumeMessage(src, dest) == [network EXCEPT ![src, dest] = Null]

OtherNodes(n) == Nodes \ {n}

\* This isn't in the Java code, but it avoids increasing the state space with what I think are irrelevant values
\* for these fields at certain transition points, e.g., transitioning back to INIT after an error or to CANVASS.
ResetUnusedFields(n) ==
    /\ election_replicationStopPosition' = [election_replicationStopPosition EXCEPT ![n] = NullValue]
    /\ election_replicationLeadershipTermId' = [election_replicationLeadershipTermId EXCEPT ![n] = NullValue]
    /\ election_replicationTermBaseLogPosition' = [election_replicationTermBaseLogPosition EXCEPT ![n] = NullValue]
    /\ election_logSubscription' = [election_logSubscription EXCEPT ![n] = Null]
    /\ election_catchupJoinPosition' = [election_catchupJoinPosition EXCEPT ![n] = NullValue]
    /\ logReplication' = [logReplication EXCEPT ![n] = Null]
    /\ logReplay' = [logReplay EXCEPT ![n] = Null]

\* This isn't in the Java code, but it avoids increasing the state space with what I think are irrelevant values
\* for these fields when an election is completed.
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
    /\ logReplication' = [logReplication EXCEPT ![n] = Null]
    /\ logReplay' = [logReplay EXCEPT ![n] = Null]
    /\ clusterMembers_isBallotSent' = [ clusterMembers_isBallotSent EXCEPT ![n] = [ m \in Nodes |-> FALSE ] ]
    /\ clusterMembers_vote' = [ clusterMembers_vote EXCEPT ![n] = [ m \in Nodes |-> Null ] ]

\* Models the transition to CANVASS from other states, which resets members etc.
Election_State_CANVASS(n, timeoutCount) ==
    /\ \/ timeoutCount = 0
       \/ leadershipTermId[n] > 0 \* STATE SPACE GUARD
    /\ checker_timeoutCount + timeoutCount < MaxTimeoutCount \* STATE SPACE GUARD
    /\ election_state' = [election_state EXCEPT ![n] = "CANVASS"]
    /\ clusterMembers_isBallotSent' = [ clusterMembers_isBallotSent EXCEPT ![n] = [ m \in Nodes |-> FALSE ] ]
    /\ clusterMembers_vote' = [ clusterMembers_vote EXCEPT ![n] = [ m \in Nodes |-> Null ] ]
    /\ clusterMembers_candidateTermId' = [ clusterMembers_candidateTermId EXCEPT ![n] = [ m \in Nodes |-> NullValue ] ]
    /\ clusterMembers_leadershipTermId' = [ clusterMembers_leadershipTermId EXCEPT ![n] =
                                                 [ m \in Nodes |-> IF m = n THEN election_leadershipTermId[n] ELSE NullValue ] ]
    /\ clusterMembers_logPosition' = [ clusterMembers_logPosition EXCEPT ![n] =
                                                 [ m \in Nodes |-> IF m = n THEN election_logPosition[n] ELSE NullValue ] ]
    /\ election_leaderMember' = [election_leaderMember EXCEPT ![n] = Null]
    /\ role' = [role EXCEPT ![n] = "FOLLOWER"]
    /\ ResetUnusedFields(n)
    /\ checker_timeoutCount' = checker_timeoutCount + timeoutCount

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

\* Models the handling of exceptions thrown by Election#doWork
Election_HandleError(n) ==
    /\ election_logPosition' = [election_logPosition EXCEPT ![n] = commitPosition[n]]
    /\ Election_State_CANVASS(n, 1)
    /\ election_notifiedCommitPosition' = [election_candidateTermId EXCEPT ![n] = 0]
    /\ election_candidateTermId' = [election_candidateTermId EXCEPT ![n] = Max({nodeStateFile_candidateTermId[n], election_leadershipTermId[n]})]
    /\ election_appendPosition' = [election_appendPosition EXCEPT ![n] = Len(log[n])]
    /\ commitPosition' = [commitPosition EXCEPT ![n] = election_logPosition[n]]

Election_PublishCanvassPosition(n) ==
    /\ Broadcast(network, [from |-> n,
                           type |-> "CanvassPosition",
                           logLeadershipTermId |-> election_logLeadershipTermId[n],
                           appendPosition |-> election_appendPosition[n],
                           logPosition |-> election_logPosition[n]])
    /\ UNCHANGED <<persistent_state, module_fields, election_state, election_fields, member_fields, checker_vars>>

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
          /\ UNCHANGED <<persistent_state, module_fields, election_fields, member_fields, network, checker_vars>>

NodeStateFile_ProposeMaxCandidateTermId(n, candidateTermId, logPosition) ==
    LET newCandidateTermId == Max({candidateTermId, nodeStateFile_candidateTermId[n]})
        newLogPosition == IF candidateTermId > nodeStateFile_candidateTermId[n] THEN logPosition ELSE nodeStateFile_logPosition[n]
    IN /\ newCandidateTermId <= MaxLeadershipTerm \* STATE SPACE GUARD
       /\ nodeStateFile_candidateTermId' = [nodeStateFile_candidateTermId EXCEPT ![n] = newCandidateTermId ]
       /\ nodeStateFile_logPosition' = [nodeStateFile_logPosition EXCEPT ![n] = newLogPosition]
       /\ election_candidateTermId' = [election_candidateTermId EXCEPT ![n] = newCandidateTermId]

ClusterMember_BecomeCandidate(n, candidateTermId) ==
    /\ clusterMembers_isBallotSent' = [ clusterMembers_isBallotSent EXCEPT ![n] = [ m \in Nodes |-> n = m ] ]
    /\ clusterMembers_candidateTermId' = [ clusterMembers_candidateTermId EXCEPT ![n] = [ m \in Nodes |-> IF n = m THEN candidateTermId ELSE NullValue ] ]
    /\ clusterMembers_vote' = [ clusterMembers_vote EXCEPT ![n] = [ m \in Nodes |-> IF n = m THEN TRUE ELSE Null ] ]

Election_Nominate(n) ==
    /\ election_state[n] = "NOMINATE"
    /\ \/ Election_PublishCanvassPosition(n)
       \/ LET newCandidateTermId == Max({election_candidateTermId[n] + 1, nodeStateFile_candidateTermId[n]})
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
                            clusterMembers_leadershipTermId, clusterMembers_logPosition, network, checker_vars>>

IsQuorumLeader(n) ==
    /\ Cardinality({ m \in Nodes: clusterMembers_vote[n][m] = TRUE}) >= QuorumSize
    /\ \A m \in Nodes : clusterMembers_vote[n][m] /= FALSE

Election_CandidateBallot(n) ==
    /\ election_state[n] = "CANDIDATE_BALLOT"
    /\ \/ /\ IsQuorumLeader(n)
          /\ election_leaderMember' = [ election_leaderMember EXCEPT ![n] = n ]
          /\ election_leadershipTermId' = [ election_leadershipTermId EXCEPT ![n] = election_candidateTermId[n] ]
          /\ Election_State_LEADER_LOG_REPLICATION(n)
          /\ UNCHANGED <<persistent_state, commitPosition, leaderMember, logReplay, leadershipTermId,
                         logReplication, notifiedCommitPosition,
                         election_logPosition, election_appendPosition,
                         election_logLeadershipTermId, election_candidateTermId, election_notifiedCommitPosition,
                         election_catchupJoinPosition, election_logSubscription,
                         election_replicationLeadershipTermId, election_replicationStopPosition,
                         election_replicationTermBaseLogPosition,
                         member_fields, network, checker_vars>>
       \/ /\ Election_State_CANVASS(n, 1)
          /\ UNCHANGED <<persistent_state, commitPosition, leaderMember, leadershipTermId,
                         notifiedCommitPosition,
                         election_logPosition, election_appendPosition, election_logLeadershipTermId,
                         election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition,
                         network>>
       \/ /\ \A m \in OtherNodes(n) : clusterMembers_isBallotSent[n][m] = FALSE
          /\ Broadcast(network, [type |-> "RequestVote",
                                 from |-> n,
                                 logLeadershipTermId |-> election_logLeadershipTermId[n],
                                 logPosition |-> election_appendPosition[n],
                                 candidateTermId |-> election_candidateTermId[n]])
          /\ clusterMembers_isBallotSent' = [clusterMembers_isBallotSent EXCEPT ![n] = [m \in Nodes |-> TRUE]]
          /\ UNCHANGED <<persistent_state, module_fields, election_state, election_fields,
                         clusterMembers_vote, clusterMembers_candidateTermId,
                         clusterMembers_leadershipTermId, clusterMembers_logPosition, checker_vars>>

Election_FollowerBallot(n) ==
    /\ election_state[n] = "FOLLOWER_BALLOT"
    /\ Election_State_CANVASS(n, 1)
    /\ UNCHANGED <<persistent_state, commitPosition, leaderMember, leadershipTermId,
                   notifiedCommitPosition,
                   election_logPosition, election_appendPosition, election_logLeadershipTermId,
                   election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition, network>>

NodesSeq == SetToSeq(Nodes)
MaxQuorumPosition(n) ==
    LET sortedNodes == SortSeq(NodesSeq, LAMBDA x, y : clusterMembers_logPosition[n][x] > clusterMembers_logPosition[n][y])
    IN clusterMembers_logPosition[n][sortedNodes[QuorumSize]]

LogReplication_IsDone(replication) ==
    replication /= Null /\ replication.position >= replication.stopPosition

LogReplay_IsDone(replay) ==
    replay /= Null /\ replay.replayPos >= replay.stopPos

RecordingLog_FindTermEntry(n, termId) ==
    IF termId \in DOMAIN recordingLog[n] THEN recordingLog[n][termId]
    ELSE Null

RecordingLog_EnsureCoherent(n, termId, termBaseLogPosition, logPosition) ==
    LET existingTerms == DOMAIN recordingLog[n]
        maxExistingTerm == Max(existingTerms \union {-1})
        maxTerm == Max({maxExistingTerm, termId})
        newTerms == 0..maxTerm
    IN recordingLog' = [recordingLog EXCEPT ![n] =
        [i \in newTerms |->
            IF i = maxExistingTerm /\ recordingLog[n][i].logPosition = NullValue THEN
                [recordingLog[n][i] EXCEPT !.logPosition = termBaseLogPosition]
            ELSE IF i <= maxExistingTerm THEN
                recordingLog[n][i]
            ELSE IF i < termId THEN
                [leadershipTermId |-> i,
                 termBaseLogPosition |-> termBaseLogPosition, \* TODO model initialTermBaseLogPosition for i=0?
                 logPosition |-> termBaseLogPosition]
            ELSE
                [leadershipTermId |-> i,
                 termBaseLogPosition |-> termBaseLogPosition, \* TODO model initialTermBaseLogPosition for i=0?
                 logPosition |-> logPosition]
        ]
    ]

Election_OnReplayNewLeadershipTermEvent(n, termId, logPosition, termBaseLogPosition) ==
    /\ RecordingLog_EnsureCoherent(n, termId, termBaseLogPosition, NullValue)
    /\ election_logPosition' = [election_logPosition EXCEPT ![n] = logPosition]
    /\ election_logLeadershipTermId' = [election_logLeadershipTermId EXCEPT ![n] = termId]

CM_OnReplayNewLeadershipTermEvent(n, termId, logPosition, termBaseLogPosition) ==
    /\ leadershipTermId' = [leadershipTermId EXCEPT ![n] = termId]
    /\ \/ /\ election_state[n] \in {"FOLLOWER_CATCHUP", "FOLLOWER_REPLAY"}
          /\ Election_OnReplayNewLeadershipTermEvent(n, termId, logPosition, termBaseLogPosition)
       \/ /\ election_state[n] \notin {"FOLLOWER_CATCHUP", "FOLLOWER_REPLAY"}
          /\ UNCHANGED <<recordingLog, election_logPosition, election_logLeadershipTermId, checker_vars>>

Election_PublishNewLeadershipTermOnInterval(n, quorumPos) ==
    /\ LET entry == RecordingLog_FindTermEntry(n, election_leadershipTermId[n]) IN
       LET nextLeadershipTermId == IF entry = Null THEN election_leadershipTermId[n] ELSE entry.leadershipTermId + 1 IN
       LET nextTermBaseLogPosition == IF entry = Null THEN election_appendPosition[n] ELSE entry.termBaseLogPosition IN
       LET nextLogPosition == IF entry = Null THEN NullValue
                              ELSE IF entry.logPosition = NullValue THEN election_appendPosition[n]
                              ELSE entry.logPosition IN
       Broadcast(network, [type |-> "NewLeadershipTerm",
                           from |-> n,
                           logLeadershipTermId |-> election_logLeadershipTermId[n],
                           nextLeadershipTermId |-> nextLeadershipTermId,
                           nextTermBaseLogPosition |-> nextTermBaseLogPosition,
                           nextLogPosition |-> nextLogPosition,
                           leadershipTermId |-> election_leadershipTermId[n],
                           termBaseLogPosition |-> election_appendPosition[n],
                           logPosition |-> election_appendPosition[n],
                           commitPosition |-> quorumPos,
                           leaderMember |-> n ])

CM_PublishCommitPosition(n, quorumPos, termId) ==
    Broadcast(network, [type |-> "CommitPosition",
                        from |-> n,
                        leadershipTermId |-> termId,
                        logPosition |-> quorumPos,
                        leaderMember |-> n ])

Election_PublishCommitPositionOnInterval(n, quorumPos) ==
    CM_PublishCommitPosition(n, quorumPos, election_leadershipTermId[n])

CM_QuorumPositionBoundedByLeaderLog0(n, leaderAppendPosition) ==
    Min({leaderAppendPosition, MaxQuorumPosition(n)})

CM_QuorumPositionBoundedByLeaderLog1(n) ==
    CM_QuorumPositionBoundedByLeaderLog0(n, election_appendPosition[n])

Election_LeaderLogReplication(n) ==
    /\ election_state[n] = "LEADER_LOG_REPLICATION"
    /\ clusterMembers_logPosition' = [ clusterMembers_logPosition EXCEPT ![n][n] = election_appendPosition[n]]
    /\ LET quorumPos == CM_QuorumPositionBoundedByLeaderLog1(n)
       IN \/ /\ quorumPos >= election_appendPosition[n]
             /\ election_state' = [ election_state EXCEPT ![n] = "LEADER_REPLAY" ]
             /\ UNCHANGED <<persistent_state, module_fields, election_fields, clusterMembers_vote,
                            clusterMembers_candidateTermId, clusterMembers_isBallotSent,
                            clusterMembers_leadershipTermId, network, checker_vars>>
          \/ /\ Election_PublishNewLeadershipTermOnInterval(n, quorumPos)
             /\ UNCHANGED <<persistent_state, module_fields, election_state, election_fields,
                            clusterMembers_vote, clusterMembers_candidateTermId,
                            clusterMembers_isBallotSent, clusterMembers_leadershipTermId, checker_vars>>
          \/ /\ Election_PublishCommitPositionOnInterval(n, quorumPos)
             /\ UNCHANGED <<persistent_state, module_fields, election_state,
                            election_logPosition, election_appendPosition,
                            election_logLeadershipTermId, election_leadershipTermId,
                            election_candidateTermId, election_notifiedCommitPosition,
                            election_leaderMember,
                            election_catchupJoinPosition, election_logSubscription,
                            election_replicationLeadershipTermId, election_replicationStopPosition,
                            election_replicationTermBaseLogPosition,
                            clusterMembers_vote, clusterMembers_candidateTermId,
                            clusterMembers_isBallotSent, clusterMembers_leadershipTermId, checker_vars>>

Election_LeaderReplay(n) ==
    /\ election_state[n] = "LEADER_REPLAY"
    /\ \/ /\ logReplay[n] = Null
          /\ clusterMembers_leadershipTermId' = [ clusterMembers_leadershipTermId EXCEPT ![n][n] = election_leadershipTermId[n] ]
          /\ clusterMembers_logPosition' = [ clusterMembers_logPosition EXCEPT ![n][n] = election_appendPosition[n] ]
          /\ \/ /\ election_appendPosition[n] > election_logPosition[n]
                /\ logReplay' = [ logReplay EXCEPT ![n] = [ replayPos |-> election_logPosition[n], stopPos |-> election_appendPosition[n] ] ]
                /\ UNCHANGED <<persistent_state, role, commitPosition, leaderMember, leadershipTermId,
                               notifiedCommitPosition,
                               logReplication, election_state, election_fields,
                               clusterMembers_vote, clusterMembers_candidateTermId,
                               clusterMembers_isBallotSent, network, checker_vars>>
             \/ /\ election_appendPosition[n] <= election_logPosition[n]
                /\ election_state' = [ election_state EXCEPT ![n] = "LEADER_INIT" ]
                /\ UNCHANGED <<persistent_state, module_fields, election_fields,
                               clusterMembers_vote, clusterMembers_candidateTermId,
                               clusterMembers_isBallotSent, network, checker_vars>>
       \/ /\ logReplay[n] /= Null
          /\ logReplay[n].stopPos <= logReplay[n].replayPos
          /\ logReplay' = [ logReplay EXCEPT ![n] = Null ]
          /\ election_logPosition' = [ election_logPosition EXCEPT ![n] = election_appendPosition[n] ]
          /\ election_state' = [ election_state EXCEPT ![n] = "LEADER_INIT" ]
          /\ UNCHANGED <<persistent_state, role, commitPosition, leaderMember, leadershipTermId,
                         notifiedCommitPosition,
                         logReplication, election_appendPosition,
                         election_logLeadershipTermId, election_leadershipTermId,
                         election_candidateTermId, election_notifiedCommitPosition,
                         election_leaderMember,
                         election_catchupJoinPosition, election_logSubscription,
                         election_replicationLeadershipTermId, election_replicationStopPosition,
                         election_replicationTermBaseLogPosition,
                         member_fields, network, checker_vars>>
       \/ /\ Election_PublishNewLeadershipTermOnInterval(n, CM_QuorumPositionBoundedByLeaderLog1(n))
          /\ UNCHANGED <<persistent_state, module_fields, election_state, election_fields, member_fields, checker_vars>>
       \/ /\ Election_PublishCommitPositionOnInterval(n, CM_QuorumPositionBoundedByLeaderLog1(n))
          /\ UNCHANGED <<persistent_state, module_fields, election_state,
                         election_logPosition, election_appendPosition,
                         election_logLeadershipTermId, election_leadershipTermId,
                         election_candidateTermId, election_notifiedCommitPosition,
                         election_leaderMember,
                         election_catchupJoinPosition, election_logSubscription,
                         election_replicationLeadershipTermId, election_replicationStopPosition,
                         election_replicationTermBaseLogPosition,
                         member_fields, checker_vars>>

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
                   member_fields, network, checker_vars>>

ClusterMember_HasQuorumAtPosition(n) ==
    Cardinality({ m \in Nodes: /\ clusterMembers_leadershipTermId[n][m] = election_leadershipTermId[n]
                               /\ clusterMembers_logPosition[n][m] >= election_logPosition[n]}) >= QuorumSize

CM_UpdateLeaderPosition(n, appendPos, quorumPos) ==
    /\ clusterMembers_logPosition' = [clusterMembers_logPosition EXCEPT ![n][n] = appendPos]
    /\ \/ /\ quorumPos > commitPosition[n]
          /\ CM_PublishCommitPosition(n, quorumPos, leadershipTermId[n])
          /\ commitPosition' = [commitPosition EXCEPT ![n] = quorumPos]
          /\ UNCHANGED <<persistent_state, role, leaderMember, logReplay, leadershipTermId,
                         logReplication, notifiedCommitPosition,
                         election_state, election_fields,
                         clusterMembers_vote, clusterMembers_candidateTermId,
                         clusterMembers_isBallotSent, clusterMembers_leadershipTermId, checker_vars>>
       \/ /\ quorumPos <= commitPosition[n]
          /\ UNCHANGED <<persistent_state, module_fields, election_state, election_fields,
                         clusterMembers_vote, clusterMembers_candidateTermId,
                         clusterMembers_isBallotSent, clusterMembers_leadershipTermId, network, checker_vars>>

CM_ElectionComplete(n) ==
    /\ leadershipTermId' = [leadershipTermId EXCEPT ![n] = election_leadershipTermId[n]]
    /\ commitPosition' = [commitPosition EXCEPT ![n] = election_logPosition[n]]
    /\ notifiedCommitPosition' = [notifiedCommitPosition EXCEPT ![n] = Max({election_logPosition[n], notifiedCommitPosition[n]})]
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
                    leadershipTermId |-> election_leadershipTermId[n],
                    logPosition |-> election_logPosition[n],
                    leaderMember |-> n,
                    termBaseLogPosition |-> election_appendPosition[n]
                ])]
             /\ election_state' = [election_state EXCEPT ![n] = "CLOSED"]
             /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, recordingLog,
                            role, election_logSubscription, clusterMembers_candidateTermId,
                            clusterMembers_leadershipTermId, clusterMembers_logPosition,
                            network, checker_vars>>
          \/ CM_UpdateLeaderPosition(n, election_appendPosition[n], quorumPos)
          \/ /\ Election_PublishNewLeadershipTermOnInterval(n, quorumPos)
             /\ UNCHANGED <<persistent_state, module_fields, election_state, election_fields, member_fields, checker_vars>>

Election_PublishFollowerReplicationPosition(n) ==
    /\ Send(network, [type |-> "AppendPosition",
                      from |-> n,
                      to |-> election_leaderMember[n],
                      leadershipTermId |-> election_replicationLeadershipTermId[n],
                      logPosition |-> election_appendPosition[n],
                      leaderMember |-> election_leaderMember[n]])
    /\ UNCHANGED <<persistent_state, module_fields, election_state,
                   election_logPosition, election_appendPosition,
                   election_logLeadershipTermId, election_leadershipTermId,
                   election_candidateTermId, election_notifiedCommitPosition,
                   election_leaderMember,
                   election_catchupJoinPosition, election_logSubscription,
                   election_replicationLeadershipTermId, election_replicationStopPosition,
                   election_replicationTermBaseLogPosition,
                   member_fields, checker_vars>>

Election_PublishFollowerAppendPosition(n) ==
    /\ Send(network, [type |-> "AppendPosition",
                      from |-> n,
                      to |-> election_leaderMember[n],
                      leadershipTermId |-> election_leadershipTermId[n],
                      logPosition |-> election_appendPosition[n],
                      leaderMember |-> election_leaderMember[n]])
    /\ UNCHANGED <<persistent_state, module_fields, election_state,
                   election_logPosition, election_appendPosition,
                   election_logLeadershipTermId, election_leadershipTermId,
                   election_candidateTermId, election_notifiedCommitPosition,
                   election_leaderMember,
                   election_catchupJoinPosition, election_logSubscription,
                   election_replicationLeadershipTermId, election_replicationStopPosition,
                   election_replicationTermBaseLogPosition,
                   member_fields, checker_vars>>

Election_FollowerLogReplication(n) ==
    /\ election_state[n] = "FOLLOWER_LOG_REPLICATION"
    /\ \/ /\ logReplication[n] = Null
          /\ \/ /\ election_appendPosition[n] < election_replicationStopPosition[n]
                /\ logReplication' = [logReplication EXCEPT ![n] = [
                       position |-> election_appendPosition[n],
                       stopPosition |-> election_replicationStopPosition[n],
                       sourceMember |-> election_leaderMember[n]
                   ]]
                /\ UNCHANGED <<persistent_state, role, commitPosition, leaderMember, logReplay,
                               leadershipTermId, notifiedCommitPosition, election_state,
                               election_logPosition, election_appendPosition,
                               election_logLeadershipTermId, election_leadershipTermId,
                               election_candidateTermId, election_notifiedCommitPosition, election_leaderMember,
                               election_catchupJoinPosition, election_logSubscription,
                               election_replicationStopPosition, election_replicationLeadershipTermId, election_replicationTermBaseLogPosition,
                               member_fields, network, checker_vars>>
             \/ /\ election_appendPosition[n] >= election_replicationStopPosition[n]
                /\ RecordingLog_EnsureCoherent(n, election_replicationLeadershipTermId[n], election_replicationTermBaseLogPosition[n], election_replicationStopPosition[n])
                /\ election_logLeadershipTermId' = [election_logLeadershipTermId EXCEPT ![n] = election_replicationLeadershipTermId[n]]
                /\ Election_State_CANVASS(n, 0)
                /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, log,
                               commitPosition, leaderMember, leadershipTermId,
                               notifiedCommitPosition,
                               election_logPosition, election_appendPosition, election_leadershipTermId,
                               election_candidateTermId, election_notifiedCommitPosition, network>>
       \/ /\ logReplication[n] /= Null
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
                               leadershipTermId, notifiedCommitPosition, election_state, election_fields,
                               member_fields, network, checker_vars>>
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
       \/ /\ logReplication[n] /= Null
          /\ Election_PublishFollowerReplicationPosition(n)
       \/ /\ LogReplication_IsDone(logReplication[n])
          /\ election_notifiedCommitPosition[n] < election_appendPosition[n]
          /\ Election_HandleError(n)
          /\ UNCHANGED <<persistent_state, leaderMember, leadershipTermId,
                         notifiedCommitPosition, election_logLeadershipTermId, election_leadershipTermId, network>>

Election_FollowerReplay(n) ==
    /\ election_state[n] = "FOLLOWER_REPLAY"
    /\ \/ /\ logReplay[n] = Null
          /\ \/ /\ election_logPosition[n] < election_appendPosition[n]
                /\ election_notifiedCommitPosition[n] = 0
                /\ Election_PublishFollowerAppendPosition(n)
             \/ /\ election_logPosition[n] < election_appendPosition[n]
                /\ election_notifiedCommitPosition[n] /= 0
                /\ election_logPosition[n] >= election_notifiedCommitPosition[n]
                /\ Election_State_CANVASS(n, 0)
                /\ UNCHANGED <<persistent_state, commitPosition, leaderMember, leadershipTermId,
                               notifiedCommitPosition,
                               election_logPosition, election_appendPosition, election_logLeadershipTermId,
                               election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition,
                               network>>
             \/ /\ election_logPosition[n] < election_appendPosition[n]
                /\ election_notifiedCommitPosition[n] /= 0
                /\ election_logPosition[n] < election_notifiedCommitPosition[n]
                /\ logReplay' = [logReplay EXCEPT ![n] = [
                       replayPos |-> election_logPosition[n],
                       stopPos |-> Min({election_appendPosition[n], election_notifiedCommitPosition[n]})
                   ]]
                /\ UNCHANGED <<persistent_state, role, commitPosition, leaderMember, leadershipTermId,
                               logReplication, notifiedCommitPosition, election_state,
                               election_fields, member_fields, network, checker_vars>>
             \/ /\ election_logPosition[n] >= election_appendPosition[n]
                /\ election_state' = [election_state EXCEPT ![n] =
                       IF election_catchupJoinPosition[n] /= NullValue
                       THEN "FOLLOWER_CATCHUP_INIT"
                       ELSE "FOLLOWER_LOG_INIT"]
                /\ UNCHANGED <<persistent_state, module_fields, election_fields, member_fields, network, checker_vars>>
       \/ /\ logReplay[n] /= Null
          /\ ~LogReplay_IsDone(logReplay[n])
          /\ LET currentPos == logReplay[n].replayPos + 1
                 logEntry == IF Len(log[n]) >= currentPos THEN log[n][currentPos] ELSE Null
             IN /\ logEntry /= Null
                /\ logReplay' = [logReplay EXCEPT ![n].replayPos = currentPos]
                /\ commitPosition' = [commitPosition EXCEPT ![n] = Max({commitPosition[n], currentPos})]
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
                                     member_fields, network, checker_vars>>
                   \/ /\ logEntry.type /= "NewLeadershipTerm"
                      /\ UNCHANGED <<persistent_state, role, leaderMember, leadershipTermId, logReplication,
                                     notifiedCommitPosition,
                                     election_state, election_fields, member_fields, network, checker_vars>>
       \/ /\ LogReplay_IsDone(logReplay[n])
          /\ election_logPosition' = [election_logPosition EXCEPT ![n] = logReplay[n].replayPos]
          /\ logReplay' = [logReplay EXCEPT ![n] = Null]
          /\ \/ /\ logReplay[n].replayPos = election_appendPosition[n]
                /\ election_catchupJoinPosition[n] /= NullValue
                /\ election_state' = [election_state EXCEPT ![n] = "FOLLOWER_CATCHUP_INIT"]
                /\ UNCHANGED <<persistent_state, role, commitPosition, leaderMember, leadershipTermId,
                               logReplication, notifiedCommitPosition,
                               election_appendPosition, election_logLeadershipTermId,
                               election_leadershipTermId, election_candidateTermId,
                               election_notifiedCommitPosition,
                               election_leaderMember, election_catchupJoinPosition, election_logSubscription,
                               election_replicationLeadershipTermId, election_replicationStopPosition,
                               election_replicationTermBaseLogPosition,
                               member_fields, network, checker_vars>>
             \/ /\ logReplay[n].replayPos = election_appendPosition[n]
                /\ election_catchupJoinPosition[n] = NullValue
                /\ election_state' = [election_state EXCEPT ![n] = "FOLLOWER_LOG_INIT"]
                /\ UNCHANGED <<persistent_state, role, commitPosition, leaderMember, leadershipTermId,
                               logReplication, notifiedCommitPosition,
                               election_appendPosition, election_logLeadershipTermId,
                               election_leadershipTermId, election_candidateTermId,
                               election_notifiedCommitPosition,
                               election_leaderMember, election_catchupJoinPosition, election_logSubscription,
                               election_replicationLeadershipTermId, election_replicationStopPosition,
                               election_replicationTermBaseLogPosition,
                               member_fields, network, checker_vars>>
             \/ /\ logReplay[n].replayPos /= election_appendPosition[n]
                /\ Election_State_CANVASS(n, 1)
                /\ UNCHANGED <<persistent_state, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition,
                               election_appendPosition, election_logLeadershipTermId,
                               election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition,
                               network>>

Election_FollowerCatchupInit(n) ==
    /\ election_state[n] = "FOLLOWER_CATCHUP_INIT"
    /\ \/ /\ election_leaderMember[n] /= Null
          /\ election_logSubscription' = [election_logSubscription EXCEPT ![n] = [ source |-> election_leaderMember[n],
                                                                                   position |-> Null ] ]
          /\ Send(network, [type |-> "CatchupPosition",
                            from |-> n,
                            to |-> election_leaderMember[n],
                            leadershipTermId |-> election_leadershipTermId[n],
                            logPosition |-> election_logPosition[n]])
          /\ election_state' = [election_state EXCEPT ![n] = "FOLLOWER_CATCHUP_AWAIT"]
          /\ UNCHANGED <<persistent_state, module_fields, election_logPosition, election_appendPosition,
                         election_logLeadershipTermId, election_leadershipTermId,
                         election_candidateTermId, election_notifiedCommitPosition,
                         election_leaderMember,
                         election_catchupJoinPosition,
                         election_replicationLeadershipTermId, election_replicationStopPosition,
                         election_replicationTermBaseLogPosition,
                         member_fields, checker_vars>>
       \/ /\ Election_HandleError(n)
          /\ UNCHANGED <<persistent_state, leaderMember, leadershipTermId,
                         notifiedCommitPosition, election_logLeadershipTermId, election_leadershipTermId, network>>

Election_FollowerCatchupAwait(n) ==
    /\ election_state[n] = "FOLLOWER_CATCHUP_AWAIT"
    /\ \/ /\ election_logSubscription[n] /= Null
          /\ election_logSubscription[n].position /= Null
          /\ election_logSubscription[n].position = election_logPosition[n]
          /\ election_state' = [election_state EXCEPT ![n] = "FOLLOWER_CATCHUP"]
          /\ UNCHANGED <<persistent_state, module_fields, election_logPosition, election_appendPosition,
                         election_logLeadershipTermId, election_leadershipTermId,
                         election_candidateTermId, election_notifiedCommitPosition,
                         election_leaderMember,
                         election_catchupJoinPosition, election_logSubscription,
                         election_replicationLeadershipTermId, election_replicationStopPosition,
                         election_replicationTermBaseLogPosition,
                         member_fields, network, checker_vars>>
       \/ /\ election_logSubscription[n] = Null \/ election_logSubscription[n].position = Null
          /\ Election_HandleError(n)
          /\ UNCHANGED <<persistent_state, leaderMember, leadershipTermId,
                         notifiedCommitPosition, election_logLeadershipTermId, election_leadershipTermId, network>>

CM_UpdateFollowerPosition(n, leader) ==
    LET position == Len(log[n])
    IN /\ Send(network, [type |-> "AppendPosition",
                         from |-> n,
                         to |-> leader,
                         leadershipTermId |-> leadershipTermId[n],
                         logPosition |-> position])
       /\ UNCHANGED <<persistent_state, role, commitPosition, leaderMember, logReplay, leadershipTermId,
                      logReplication, notifiedCommitPosition, election_state, election_fields, member_fields,
                      checker_vars>>

Election_FollowerCatchup(n) ==
    /\ election_state[n] = "FOLLOWER_CATCHUP"
    /\ \/ LET newPosition == election_logSubscription[n].position + 1
              remoteLogLength == Len(log[election_logSubscription[n].source])
              newEntry == IF remoteLogLength >= newPosition
                          THEN log[election_logSubscription[n].source][newPosition]
                          ELSE Null
          IN /\ newEntry /= Null
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
                                  member_fields, network, checker_vars>>
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
                                  member_fields, network, checker_vars>>
       \/ CM_UpdateFollowerPosition(n, election_leaderMember[n])
       \/ /\ commitPosition[n] >= election_catchupJoinPosition[n]
          /\ commitPosition[n] >= election_notifiedCommitPosition[n]
          /\ election_appendPosition' = [election_appendPosition EXCEPT ![n] = commitPosition[n]]
          /\ election_logPosition' = [election_logPosition EXCEPT ![n] = commitPosition[n]]
          \* Note: we're deliberately not modelling the stop catchup interaction here, as it shouldn't affect
          \* the safety properties we're interested in, assuming it is corect.
          /\ election_state' = [election_state EXCEPT ![n] = "FOLLOWER_LOG_INIT"]
          /\ UNCHANGED <<persistent_state, module_fields, election_logLeadershipTermId,
                         election_leadershipTermId, election_candidateTermId,
                         election_notifiedCommitPosition,
                         election_leaderMember,
                         election_catchupJoinPosition,
                         election_logSubscription,
                         election_replicationLeadershipTermId, election_replicationStopPosition,
                         election_replicationTermBaseLogPosition,
                         member_fields, network, checker_vars>>
       \/ /\ Election_HandleError(n)
          /\ UNCHANGED <<persistent_state, leaderMember, leadershipTermId,
                         notifiedCommitPosition, election_logLeadershipTermId, election_leadershipTermId, network>>

Election_FollowerLogInit(n) ==
    /\ election_state[n] = "FOLLOWER_LOG_INIT"
    /\ \/ /\ election_logSubscription[n] = Null
          \* Note: we do NOT model the asynchronous establishment of the live subscription here, as it shouldn't be
          \* necessary to model the safety properties we're interested in.
          /\ election_logSubscription' = [election_logSubscription EXCEPT ![n] = [ source |-> election_leaderMember[n], position |-> Len(log[n]) ] ]
          /\ election_state' = [election_state EXCEPT ![n] = "FOLLOWER_LOG_AWAIT"]
          /\ UNCHANGED <<persistent_state, role, commitPosition, leaderMember, logReplay, leadershipTermId,
                         logReplication, notifiedCommitPosition,
                         election_logPosition, election_appendPosition,
                         election_logLeadershipTermId, election_leadershipTermId,
                         election_candidateTermId, election_notifiedCommitPosition,
                         election_leaderMember, election_catchupJoinPosition,
                         election_replicationLeadershipTermId, election_replicationStopPosition,
                         election_replicationTermBaseLogPosition,
                         member_fields, network, checker_vars>>
       \/ /\ election_logSubscription[n] /= Null
          /\ election_state' = [election_state EXCEPT ![n] = "FOLLOWER_READY"]
          /\ UNCHANGED <<persistent_state, module_fields, election_logPosition, election_appendPosition,
                         election_logLeadershipTermId, election_leadershipTermId,
                         election_candidateTermId, election_notifiedCommitPosition,
                         election_leaderMember,
                         election_catchupJoinPosition, election_logSubscription,
                         election_replicationLeadershipTermId, election_replicationStopPosition,
                         election_replicationTermBaseLogPosition,
                         member_fields, network, checker_vars>>

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
                         member_fields, network, checker_vars>>
       \/ /\ Election_HandleError(n)
          /\ UNCHANGED <<persistent_state, leaderMember, leadershipTermId,
                         notifiedCommitPosition, election_logLeadershipTermId, election_leadershipTermId, network>>

Election_FollowerReady(n) ==
    /\ election_state[n] = "FOLLOWER_READY"
    /\ \/ /\ Send(network, [type |-> "AppendPosition",
                            from |-> n,
                            to |-> election_leaderMember[n],
                            leadershipTermId |-> election_leadershipTermId[n],
                            logPosition |-> election_logPosition[n],
                            leaderMember |-> election_leaderMember[n]])
          /\ election_state' = [election_state EXCEPT ![n] = "CLOSED"]
          /\ CM_ElectionComplete(n)
          /\ UNCHANGED <<persistent_state, role, election_logSubscription,
                         clusterMembers_candidateTermId, clusterMembers_leadershipTermId, clusterMembers_logPosition,
                         checker_vars>>
       \/ /\ Election_HandleError(n)
          /\ UNCHANGED <<persistent_state, leaderMember, leadershipTermId,
                         notifiedCommitPosition, election_logLeadershipTermId, election_leadershipTermId, network>>

CM_EnterElection(n, timeoutCount) ==
    /\ election_logPosition' = [election_logPosition EXCEPT ![n] = commitPosition[n]]
    /\ election_appendPosition' = [election_appendPosition EXCEPT ![n] = Len(log[n])]
    /\ election_logLeadershipTermId' = [election_logLeadershipTermId EXCEPT ![n] = leadershipTermId[n]]
    /\ election_leadershipTermId' = [election_leadershipTermId EXCEPT ![n] = leadershipTermId[n]]
    /\ election_candidateTermId' = [election_candidateTermId EXCEPT ![n] = Max({nodeStateFile_candidateTermId[n], leadershipTermId[n]})]
    /\ election_notifiedCommitPosition' = [election_candidateTermId EXCEPT ![n] = 0]
    /\ Election_State_CANVASS(n, timeoutCount)

Election_OnAppendPosition(n, msg) ==
    \/ /\ msg.leadershipTermId <= election_leadershipTermId[n]
       /\ clusterMembers_logPosition' = [clusterMembers_logPosition EXCEPT ![n][msg.from] = msg.logPosition]
       /\ clusterMembers_leadershipTermId' = [clusterMembers_leadershipTermId EXCEPT ![n][msg.from] = msg.leadershipTermId]
       /\ UNCHANGED <<persistent_state, module_fields, election_state, election_fields, clusterMembers_vote,
                      clusterMembers_isBallotSent, clusterMembers_candidateTermId, checker_vars>>
    \/ /\ msg.leadershipTermId > election_leadershipTermId[n]
       /\ UNCHANGED <<persistent_state, module_fields, election_state, election_fields, member_fields, checker_vars>>

CM_OnAppendPosition(n, msg, newNetwork) ==
    /\ msg.type = "AppendPosition"
    /\ msg.to = n
    /\ network' = newNetwork
    /\ \/ /\ election_state[n] /= "CLOSED"
          /\ Election_OnAppendPosition(n, msg)
       \/ /\ election_state[n] = "CLOSED"
          /\ msg.leadershipTermId > leadershipTermId[n]
          /\ UNCHANGED <<persistent_state, module_fields, election_state, election_fields, member_fields,
                         checker_vars>>
       \/ /\ election_state[n] = "CLOSED"
          /\ msg.leadershipTermId <= leadershipTermId[n]
          /\ role[n] = "LEADER"
          /\ clusterMembers_logPosition' = [clusterMembers_logPosition EXCEPT ![n][msg.from] = msg.logPosition]
          /\ clusterMembers_leadershipTermId' = [clusterMembers_leadershipTermId EXCEPT ![n][msg.from] = msg.leadershipTermId]
          /\ UNCHANGED <<persistent_state, module_fields, election_state, election_fields, clusterMembers_vote,
                         clusterMembers_isBallotSent, clusterMembers_candidateTermId, checker_vars>>
       \/ /\ election_state[n] = "CLOSED"
          /\ msg.leadershipTermId <= leadershipTermId[n]
          /\ role[n] /= "LEADER"
          /\ UNCHANGED <<persistent_state, module_fields, election_state, election_fields, member_fields,
                         checker_vars>>

Election_PublishNewLeadershipTerm(n, destMember, logLeadershipTermId, quorumPosition, newNetwork) ==
    LET nextTermEntry == RecordingLog_FindTermEntry(n, logLeadershipTermId + 1) IN
    LET nextLeadershipTermId == IF nextTermEntry /= Null THEN nextTermEntry.leadershipTermId ELSE election_leadershipTermId[n] IN
    LET nextTermBaseLogPosition == IF nextTermEntry /= Null THEN nextTermEntry.termBaseLogPosition ELSE election_appendPosition[n] IN
    LET nextLogPosition == IF nextTermEntry /= Null
                           THEN
                                IF nextTermEntry.logPosition /= NullValue
                                THEN nextTermEntry.logPosition
                                ELSE election_appendPosition[n]
                           ELSE NullValue IN
    Send(newNetwork, [type |-> "NewLeadershipTerm",
                      from |-> n,
                      to |-> destMember,
                      logLeadershipTermId |-> logLeadershipTermId,
                      nextLeadershipTermId |-> nextLeadershipTermId,
                      nextTermBaseLogPosition |-> nextTermBaseLogPosition,
                      nextLogPosition |-> nextLogPosition,
                      leadershipTermId |-> election_leadershipTermId[n],
                      termBaseLogPosition |-> election_appendPosition[n],
                      logPosition |-> election_appendPosition[n],
                      commitPosition |-> quorumPosition,
                      leaderMember |-> n])

Election_OnCanvassPosition(n, msg, newNetwork) ==
    /\ clusterMembers_logPosition' = [clusterMembers_logPosition EXCEPT ![n][msg.from] = msg.logPosition]
    /\ clusterMembers_leadershipTermId' = [clusterMembers_leadershipTermId EXCEPT ![n][msg.from] = msg.logLeadershipTermId]
    /\ \/ /\ msg.logLeadershipTermId < election_leadershipTermId[n]
          /\ role[n] = "LEADER"
          /\ Election_PublishNewLeadershipTerm(n, msg.from, msg.logLeadershipTermId, CM_QuorumPositionBoundedByLeaderLog1(n), newNetwork)
          /\ UNCHANGED <<persistent_state, module_fields, election_state, election_fields,
                         clusterMembers_vote, clusterMembers_isBallotSent, clusterMembers_candidateTermId,
                         checker_vars>>
       \/ /\ msg.logLeadershipTermId > election_leadershipTermId[n]
          /\ election_state[n] \in {"LEADER_LOG_REPLICATION", "LEADER_READY"}
          /\ Election_HandleError(n)
          /\ network' = newNetwork
          /\ UNCHANGED <<persistent_state, leaderMember, leadershipTermId,
                         notifiedCommitPosition, election_logLeadershipTermId, election_leadershipTermId>>
       \/ /\ \/ msg.logLeadershipTermId = election_leadershipTermId[n]
             \/ /\ msg.logLeadershipTermId < election_leadershipTermId[n]
                /\ role[n] /= "LEADER"
          /\ network' = newNetwork
          /\ UNCHANGED <<persistent_state, module_fields, election_state, election_fields, clusterMembers_vote,
                         clusterMembers_isBallotSent, clusterMembers_candidateTermId, checker_vars>>

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
          /\ UNCHANGED <<persistent_state, module_fields, election_state, election_fields, member_fields,
                         checker_vars>>
       \/ /\ election_state[n] = "CLOSED"
          /\ role[n] = "LEADER"
          /\ msg.logLeadershipTermId <= leadershipTermId[n]
          /\ clusterMembers_logPosition' = [clusterMembers_logPosition EXCEPT ![n][msg.from] = msg.logPosition]
          /\ clusterMembers_leadershipTermId' = [clusterMembers_leadershipTermId EXCEPT ![n][msg.from] = msg.logLeadershipTermId]
          \* stopping catchup replay is not modelled
          /\ LET currentTermEntry == RecordingLog_FindTermEntry(n, leadershipTermId[n])
             IN \/ /\ currentTermEntry = Null
                   /\ network' = newNetwork
                   /\ UNCHANGED <<persistent_state, module_fields, election_state, election_fields, clusterMembers_vote,
                                  clusterMembers_isBallotSent, clusterMembers_candidateTermId, checker_vars>>
                \/ /\ currentTermEntry /= Null
                   /\ \/ /\ msg.logLeadershipTermId < leadershipTermId[n]
                         /\ LET nextLogEntry == RecordingLog_FindTermEntry(n, msg.logLeadershipTermId + 1)
                                nextLogLeadershipTermId == IF nextLogEntry /= Null THEN nextLogEntry.leadershipTermId
                                                           ELSE leadershipTermId[n]
                                nextTermBaseLogPosition == IF nextLogEntry /= Null THEN nextLogEntry.termBaseLogPosition
                                                           ELSE currentTermEntry.termBaseLogPosition
                                nextLogPosition == IF nextLogEntry /= Null THEN nextLogEntry.logPosition
                                                   ELSE NullValue
                            IN /\ Send(newNetwork, [type |-> "NewLeadershipTerm",
                                                    from |-> n,
                                                    to |-> msg.from,
                                                    logLeadershipTermId |-> msg.logLeadershipTermId,
                                                    nextLeadershipTermId |-> nextLogLeadershipTermId,
                                                    nextTermBaseLogPosition |-> nextTermBaseLogPosition,
                                                    nextLogPosition |-> nextLogPosition,
                                                    leadershipTermId |-> leadershipTermId[n],
                                                    termBaseLogPosition |-> currentTermEntry.termBaseLogPosition,
                                                    logPosition |-> Len(log[n]),
                                                    commitPosition |-> commitPosition[n],
                                                    leaderMember |-> n ])
                               /\ UNCHANGED <<persistent_state, module_fields, election_state, election_fields,
                                              clusterMembers_vote, clusterMembers_isBallotSent,
                                              clusterMembers_candidateTermId, checker_vars>>
                      \/ /\ Send(newNetwork, [type |-> "NewLeadershipTerm",
                                              from |-> n,
                                              to |-> msg.from,
                                              logLeadershipTermId |-> msg.logLeadershipTermId,
                                              nextLeadershipTermId |-> NullValue,
                                              nextTermBaseLogPosition |-> NullValue,
                                              nextLogPosition |-> NullValue,
                                              leadershipTermId |-> leadershipTermId[n],
                                              termBaseLogPosition |-> currentTermEntry.termBaseLogPosition,
                                              logPosition |-> Len(log[n]),
                                              commitPosition |-> commitPosition[n],
                                              leaderMember |-> n ])
                         /\ UNCHANGED <<persistent_state, module_fields, election_state, election_fields,
                                        clusterMembers_vote, clusterMembers_isBallotSent,
                                        clusterMembers_candidateTermId, checker_vars>>

CM_OnCatchupPosition(n, msg, newNetwork) ==
    /\ msg.type = "CatchupPosition"
    /\ msg.to = n
    /\ \/ /\ \/ role[n] /= "LEADER"
             \/ /\ role[n] = "LEADER"
                /\ msg.leadershipTermId > leadershipTermId[n]
          /\ network' = newNetwork
          /\ UNCHANGED <<persistent_state, module_fields, election_state, election_fields, member_fields,
                         checker_vars>>
       \/ /\ role[n] = "LEADER"
          /\ msg.leadershipTermId <= leadershipTermId[n]
          /\ election_logSubscription' = [election_logSubscription EXCEPT ![msg.from] = [ source |-> n, position |-> msg.logPosition ] ]
          /\ network' = newNetwork
          /\ UNCHANGED <<persistent_state, role, commitPosition, leaderMember, logReplay, leadershipTermId,
                         logReplication, notifiedCommitPosition, election_state,
                         election_logPosition, election_appendPosition,
                         election_logLeadershipTermId, election_leadershipTermId,
                         election_candidateTermId, election_notifiedCommitPosition,
                         election_leaderMember,
                         election_catchupJoinPosition,
                         election_replicationLeadershipTermId, election_replicationStopPosition,
                         election_replicationTermBaseLogPosition,
                         member_fields, checker_vars>>

Election_OnCommitPosition(n, msg) ==
    \/ /\ msg.from = election_leaderMember[n]
       /\ election_notifiedCommitPosition' = [election_notifiedCommitPosition EXCEPT ![n] = msg.logPosition]
       /\ UNCHANGED <<persistent_state, module_fields, election_state, election_logPosition, election_appendPosition,
                      election_logLeadershipTermId, election_leadershipTermId, election_candidateTermId,
                      election_leaderMember,
                      election_catchupJoinPosition, election_logSubscription, election_replicationLeadershipTermId,
                      election_replicationStopPosition, election_replicationTermBaseLogPosition,
                      member_fields, checker_vars>>
    \/ /\ msg.from /= election_leaderMember[n]
       /\ \/ /\ msg.leadershipTermId <= election_leadershipTermId[n]
             /\ UNCHANGED <<persistent_state, module_fields, election_state, election_fields, member_fields,
                            checker_vars>>
          \/ /\ msg.leadershipTermId > election_leadershipTermId[n]
             /\ election_state[n] = "LEADER_READY"
             /\ Election_HandleError(n)
             /\ UNCHANGED <<persistent_state, leaderMember, leadershipTermId,
                            notifiedCommitPosition, election_logLeadershipTermId, election_leadershipTermId>>

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
                      /\ UNCHANGED <<persistent_state, role, commitPosition, leaderMember, logReplay,
                                     leadershipTermId, logReplication,
                                     election_state, election_fields, member_fields, checker_vars>>
                   \/ /\ \/ msg.from /= leaderMember[n]
                         \/ role[n] /= "FOLLOWER"
                      /\ UNCHANGED <<persistent_state, module_fields, election_state, election_fields, member_fields,
                                     checker_vars>>
             \/ /\ msg.leadershipTermId < leadershipTermId[n]
                /\ UNCHANGED <<persistent_state, module_fields, election_state, election_fields, member_fields,
                               checker_vars>>
             \/ /\ msg.leadershipTermId > leadershipTermId[n]
                /\ CM_EnterElection(n, 0)
                /\ UNCHANGED <<persistent_state, notifiedCommitPosition, leaderMember, commitPosition,
                               leadershipTermId>>

Election_OnNewLeadershipTerm(n, msg) ==
    /\ \/ /\ \/ election_state[n] = "FOLLOWER_BALLOT"
             \/ election_state[n] = "CANDIDATE_BALLOT"
          /\ msg.leadershipTermId = election_candidateTermId[n]
       \/ election_state[n] = "CANVASS"
    /\ \/ /\ msg.logLeadershipTermId /= election_logLeadershipTermId[n]
          /\ Election_State_CANVASS(n, 0)
          /\ UNCHANGED <<persistent_state, commitPosition, leaderMember, leadershipTermId, notifiedCommitPosition,
                         election_logPosition, election_appendPosition, election_logLeadershipTermId,
                         election_leadershipTermId, election_candidateTermId, election_notifiedCommitPosition,
                         checker_vars>>
       \/ /\ msg.logLeadershipTermId = election_logLeadershipTermId[n]
          /\ \/ /\ msg.nextTermBaseLogPosition /= NullValue
                /\ msg.nextTermBaseLogPosition < election_appendPosition[n]
                /\ Assert(Len(log[n]) >= msg.nextTermBaseLogPosition, "Log isn't long enough to truncate (1)")
                /\ Assert(Len(log[n]) >= 1, "Log isn't long enough to truncate (2)")
                /\ log' = [log EXCEPT ![n] = SubSeq(log[n], 1, msg.nextTermBaseLogPosition)]
                /\ election_appendPosition' = [election_appendPosition EXCEPT ![n] = msg.nextTermBaseLogPosition]
                /\ LET MatchingTerm(entry) == entry.leadershipTermId = msg.logLeadershipTermId
                   IN IF \E i \in DOMAIN(recordingLog[n]) : MatchingTerm(recordingLog[n][i]) THEN
                          LET i == CHOOSE i \in DOMAIN(recordingLog[n]) : MatchingTerm(recordingLog[n][i])
                          IN recordingLog' = [recordingLog EXCEPT ![n][i].logPosition = msg.nextTermBaseLogPosition]
                      ELSE
                          recordingLog' = recordingLog
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
                      /\ election_candidateTermId' = [election_candidateTermId EXCEPT ![n] = Max({election_candidateTermId[n], msg.leadershipTermId})]
                      /\ election_notifiedCommitPosition' = [election_notifiedCommitPosition EXCEPT ![n] = Max({election_notifiedCommitPosition[n], msg.commitPosition})]
                      /\ UNCHANGED <<persistent_state, commitPosition, leaderMember, logReplay,
                                     leadershipTermId, logReplication,
                                     notifiedCommitPosition, election_logPosition, election_appendPosition,
                                     election_logLeadershipTermId, election_logSubscription,
                                     election_replicationLeadershipTermId, election_replicationStopPosition,
                                     election_replicationTermBaseLogPosition, member_fields, checker_vars>>
                   \/ /\ election_appendPosition[n] < msg.termBaseLogPosition
                      /\ \/ /\ msg.nextLeadershipTermId = NullValue
                            /\ Election_HandleError(n)
                            /\ UNCHANGED <<persistent_state, leaderMember, leadershipTermId,
                                           notifiedCommitPosition, election_logLeadershipTermId>>
                         \/ /\ msg.nextLeadershipTermId /= NullValue
                            /\ election_catchupJoinPosition' = [election_catchupJoinPosition EXCEPT ![n] = IF election_appendPosition[n] < msg.logPosition THEN msg.logPosition ELSE NullValue]
                            /\ election_leaderMember' = [election_leaderMember EXCEPT ![n] = msg.leaderMember]
                            /\ election_candidateTermId' = [election_candidateTermId EXCEPT ![n] = Max({election_candidateTermId[n], msg.leadershipTermId})]
                            /\ election_notifiedCommitPosition' = [election_notifiedCommitPosition EXCEPT ![n] = Max({election_notifiedCommitPosition[n], msg.commitPosition})]
                            /\ \/ /\ election_appendPosition[n] < msg.nextTermBaseLogPosition
                                  /\ election_replicationLeadershipTermId' = [election_replicationLeadershipTermId EXCEPT ![n] = msg.logLeadershipTermId]
                                  /\ election_replicationStopPosition' = [election_replicationStopPosition EXCEPT ![n] = msg.nextTermBaseLogPosition]
                                  /\ election_replicationTermBaseLogPosition' = [election_replicationTermBaseLogPosition EXCEPT ![n] = NullValue]
                                  /\ Election_State_FOLLOWER_LOG_REPLICATION(n)
                                  /\ UNCHANGED <<persistent_state, commitPosition, leaderMember, logReplay,
                                                 leadershipTermId, logReplication,
                                                 notifiedCommitPosition, election_logPosition, election_appendPosition,
                                                 election_logLeadershipTermId, election_logSubscription,
                                                 member_fields, checker_vars>>
                               \/ /\ election_appendPosition[n] = msg.nextTermBaseLogPosition
                                  /\ msg.nextLogPosition /= NullValue
                                  /\ election_replicationLeadershipTermId' = [election_replicationLeadershipTermId EXCEPT ![n] = msg.nextLeadershipTermId]
                                  /\ election_replicationStopPosition' = [election_replicationStopPosition EXCEPT ![n] = msg.nextLogPosition]
                                  /\ election_replicationTermBaseLogPosition' = [election_replicationTermBaseLogPosition EXCEPT ![n] = msg.nextTermBaseLogPosition]
                                  /\ Election_State_FOLLOWER_LOG_REPLICATION(n)
                                  /\ UNCHANGED <<persistent_state, commitPosition, leaderMember, logReplay,
                                                 leadershipTermId, logReplication,
                                                 notifiedCommitPosition, election_logPosition, election_appendPosition,
                                                 election_logLeadershipTermId, election_logSubscription,
                                                 member_fields, checker_vars>>
                               \/ /\ \/ election_appendPosition[n] > msg.nextTermBaseLogPosition
                                     \/ /\ election_appendPosition[n] = msg.nextTermBaseLogPosition
                                        /\ msg.nextLogPosition = NullValue
                                  /\ UNCHANGED <<persistent_state, role, commitPosition, leaderMember, logReplay,
                                                 leadershipTermId, logReplication,
                                                 notifiedCommitPosition, election_state, election_logPosition,
                                                 election_appendPosition, election_logLeadershipTermId,
                                                 election_logSubscription, election_replicationLeadershipTermId,
                                                 election_replicationStopPosition, election_replicationTermBaseLogPosition,
                                                 member_fields, checker_vars>>

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
                /\ notifiedCommitPosition' = [notifiedCommitPosition EXCEPT ![n] = Max({msg.commitPosition, notifiedCommitPosition[n]})]
                /\ UNCHANGED <<persistent_state, role, commitPosition, leaderMember, logReplay, leadershipTermId,
                               logReplication, election_state, election_fields, member_fields,
                               checker_vars>>
             \/ /\ msg.leadershipTermId > leadershipTermId[n]
                /\ CM_EnterElection(n, 0)
                /\ UNCHANGED <<persistent_state, notifiedCommitPosition, leaderMember, commitPosition,
                               leadershipTermId>>
             \/ /\ \/ /\ msg.leadershipTermId = leadershipTermId[n]
                      /\ \/ msg.leaderMember /= leaderMember[n]
                         \/ role[n] /= "FOLLOWER"
                   \/ msg.leadershipTermId < leadershipTermId[n]
                /\ UNCHANGED <<persistent_state, module_fields, election_state, election_fields, member_fields,
                               checker_vars>>

Election_PlaceVote(n, candidate, candidateTermId, vote, newNetwork) ==
    Send(newNetwork, [type |-> "Vote",
                      from |-> n,
                      to |-> candidate,
                      candidateTermId |-> candidateTermId,
                      logLeadershipTermId |-> election_logLeadershipTermId[n],
                      logPosition |-> election_appendPosition[n],
                      vote |-> vote])

Election_OnRequestVote(n, msg, newNetwork) ==
    \/ /\ msg.candidateTermId <= election_candidateTermId[n]
       /\ Election_PlaceVote(n, msg.from, msg.candidateTermId, FALSE, newNetwork)
       /\ UNCHANGED <<persistent_state, module_fields, election_state, election_fields, member_fields,
                      checker_vars>>
    \/ /\ msg.candidateTermId > election_candidateTermId[n]
       /\ ClusterMember_CompareLog0(election_logLeadershipTermId[n], election_appendPosition[n], msg.logLeadershipTermId, msg.logPosition) > 0
       /\ LET newCandidateTermId == Max({nodeStateFile_candidateTermId[n], msg.candidateTermId})
          IN /\ NodeStateFile_ProposeMaxCandidateTermId(n, newCandidateTermId, msg.logPosition)
             /\ Election_PlaceVote(n, msg.from, msg.candidateTermId, FALSE, newNetwork)
             /\ \/ /\ role[n] = "LEADER"
                   /\ Election_PublishNewLeadershipTerm(n, msg.from, msg.logLeadershipTermId, CM_QuorumPositionBoundedByLeaderLog1(n), newNetwork)
                   /\ UNCHANGED <<log, recordingLog, role, commitPosition, leaderMember, logReplay,
                                  leadershipTermId, logReplication, notifiedCommitPosition,
                                  election_state, election_logPosition, election_appendPosition,
                                  election_logLeadershipTermId, election_leadershipTermId, election_notifiedCommitPosition,
                                  election_leaderMember, election_catchupJoinPosition,
                                  election_logSubscription, election_replicationLeadershipTermId,
                                  election_replicationStopPosition, election_replicationTermBaseLogPosition,
                                  member_fields, checker_vars>>
                \/ /\ role[n] /= "LEADER"
                   /\ UNCHANGED <<log, recordingLog, role, commitPosition, leaderMember, logReplay,
                                  leadershipTermId, logReplication, notifiedCommitPosition,
                                  election_state, election_logPosition, election_appendPosition,
                                  election_logLeadershipTermId, election_leadershipTermId, election_notifiedCommitPosition,
                                  election_leaderMember, election_catchupJoinPosition,
                                  election_logSubscription, election_replicationLeadershipTermId,
                                  election_replicationStopPosition, election_replicationTermBaseLogPosition,
                                  member_fields, checker_vars>>
    \/ /\ msg.candidateTermId > election_candidateTermId[n]
       /\ ClusterMember_CompareLog0(election_logLeadershipTermId[n], election_appendPosition[n], msg.logLeadershipTermId, msg.logPosition) <= 0
       /\ \/ /\ election_state[n] \in {"CANVASS", "NOMINATE", "CANDIDATE_BALLOT", "FOLLOWER_BALLOT"}
             /\ NodeStateFile_ProposeMaxCandidateTermId(n, msg.candidateTermId, msg.logPosition)
             /\ Election_PlaceVote(n, msg.from, msg.candidateTermId, TRUE, newNetwork)
             /\ election_state' = [election_state EXCEPT ![n] = "FOLLOWER_BALLOT"]
             /\ UNCHANGED <<log, recordingLog, role, commitPosition, leaderMember, logReplay,
                            leadershipTermId, logReplication, notifiedCommitPosition,
                            election_logPosition, election_appendPosition,
                            election_logLeadershipTermId, election_leadershipTermId, election_notifiedCommitPosition,
                            election_leaderMember, election_catchupJoinPosition,
                            election_logSubscription, election_replicationLeadershipTermId,
                            election_replicationStopPosition, election_replicationTermBaseLogPosition,
                            member_fields, checker_vars>>
          \/ /\ election_state[n] \notin {"CANVASS", "NOMINATE", "CANDIDATE_BALLOT", "FOLLOWER_BALLOT"}
             /\ network' = newNetwork
             /\ UNCHANGED <<persistent_state, module_fields, election_state, election_fields, member_fields,
                            checker_vars>>

CM_OnRequestVote(n, msg, newNetwork) ==
    /\ msg.type = "RequestVote"
    /\ msg.to = n
    /\ \/ /\ election_state[n] /= "CLOSED"
          /\ Election_OnRequestVote(n, msg, newNetwork)
       \/ /\ election_state[n] = "CLOSED"
          /\ msg.candidateTermId > leadershipTermId[n]
          /\ network' = newNetwork
          /\ CM_EnterElection(n, 0)
          /\ UNCHANGED <<persistent_state, notifiedCommitPosition, leaderMember, commitPosition, leadershipTermId>>
       \/ /\ election_state[n] = "CLOSED"
          /\ msg.candidateTermId <= leadershipTermId[n]
          /\ network' = newNetwork
          /\ UNCHANGED <<persistent_state, module_fields, election_state, election_fields, member_fields,
                         checker_vars>>

Election_OnVote(n, msg) ==
    \/ /\ election_state[n] = "CANDIDATE_BALLOT"
       /\ msg.candidateTermId = election_candidateTermId[n]
       /\ clusterMembers_candidateTermId' = [clusterMembers_candidateTermId EXCEPT ![n][msg.from] = msg.candidateTermId]
       /\ clusterMembers_vote' = [clusterMembers_vote EXCEPT ![n][msg.from] = msg.vote]
       /\ clusterMembers_leadershipTermId' = [clusterMembers_leadershipTermId EXCEPT ![n][msg.from] = msg.logLeadershipTermId]
       /\ clusterMembers_logPosition' = [clusterMembers_logPosition EXCEPT ![n][msg.from] = msg.logPosition]
       /\ UNCHANGED <<persistent_state, module_fields, election_state, election_fields, clusterMembers_isBallotSent,
                      checker_vars>>
    \/ /\ \/ election_state[n] /= "CANDIDATE_BALLOT"
          \/ msg.candidateTermId /= election_candidateTermId[n]
       /\ UNCHANGED <<persistent_state, module_fields, election_state, election_fields, member_fields, checker_vars>>

CM_OnVote(n, msg, newNetwork) ==
    /\ msg.type = "Vote"
    /\ msg.to = n
    /\ network' = newNetwork
    /\ \/ /\ election_state[n] /= "CLOSED"
          /\ Election_OnVote(n, msg)
       \/ /\ election_state[n] = "CLOSED"
          /\ UNCHANGED<<persistent_state, module_fields, election_state, election_fields, member_fields, checker_vars>>

CM_AppendMsg(n) ==
    /\ Len(log[n]) < MaxLogLength \* STATE SPACE GUARD
    /\ \E value \in Payloads :
            LET msg == [type |-> "SessionMessage", payload |-> value ]
            IN /\ log' = [log EXCEPT ![n] = Append(@, msg)]
               /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, recordingLog, module_fields,
                              election_state, election_fields, member_fields, network, checker_vars>>

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
          \* In Java: /\ role[n] = "FOLLOWER"
          /\ \/ role[n] = "FOLLOWER"
             \/ NodeCount <= 2
          /\ CM_EnterElection(n, 1)
          /\ UNCHANGED <<persistent_state, notifiedCommitPosition, leaderMember, commitPosition, leadershipTermId,
                         network>>
       \/ /\ role[n] = "FOLLOWER"
          \* TODO: Should logSubscription be under election_? Do we need all of logSubscription, logReplay, etc.?
          /\ election_logSubscription[n] /= Null
          /\ election_logSubscription[n].position /= Null
          /\ LET newPosition == election_logSubscription[n].position + 1
                 logEntry == IF Len(log[leaderMember[n]]) >= newPosition THEN log[leaderMember[n]][newPosition] ELSE Null
             IN /\ logEntry /= Null
                /\ newPosition <= MaxLogLength \* STATE SPACE GUARD
                /\ log' = [log EXCEPT ![n] = Append(@, logEntry)]
                /\ election_logSubscription' = [election_logSubscription EXCEPT ![n].position = newPosition]
                /\ UNCHANGED <<nodeStateFile_candidateTermId, nodeStateFile_logPosition, recordingLog,
                               module_fields, election_state, election_logPosition,
                               election_appendPosition, election_logLeadershipTermId, election_leadershipTermId,
                               election_candidateTermId,
                               election_notifiedCommitPosition, election_leaderMember,
                               election_catchupJoinPosition,
                               election_replicationLeadershipTermId, election_replicationStopPosition,
                               election_replicationTermBaseLogPosition, member_fields, network, checker_vars>>
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
                                     election_replicationTermBaseLogPosition, member_fields, network, checker_vars>>
                   \/ /\ logEntry.type /= "NewLeadershipTerm"
                      /\ UNCHANGED <<persistent_state,
                                     role, leaderMember, logReplay, leadershipTermId, logReplication,
                                     notifiedCommitPosition, election_state, election_fields,
                                     member_fields, network, checker_vars>>

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

MessageLoss(src, dest) ==
    /\ network[src, dest] /= Null
    /\ network' = [network EXCEPT ![src, dest] = Null]
    /\ UNCHANGED <<persistent_state, module_fields, election_state, election_fields, member_fields, checker_vars>>

Next ==
    \/ \E n \in Nodes :
        \* Publish positions, transition to NOMINATE if a quorum of members would vote for us
        \/ Election_Canvass(n)

        \* Increment candidate term id, transition to CANDIDATE_BALLOT
        \/ Election_Nominate(n)

        \* Send request vote messages, transition to LEADER_LOG_REPLICATION if we get enough votes.
        \* Otherwise, back to CANVASS on timeout
        \/ Election_CandidateBallot(n)

        \* Back to CANVASS on timeout
        \/ Election_FollowerBallot(n)

        \* Publish leadership term and commit position, transition to LEADER_REPLAY once a quorum has
        \* replicated our (entire) log
        \/ Election_LeaderLogReplication(n)

        \* Publish leadership term and commit position, replay leadership term messages in the log,
        \* update recording log, transition to LEADER_INIT once replay is complete
        \/ Election_LeaderReplay(n)

        \* Set role to be LEADER, update recording log with new term, transition to LEADER_READY
        \/ Election_LeaderInit(n)

        \* Set leadershipTermId to the value from election, publish leadership term and "commit"
        \* position, transition to CLOSED once a quorum has replicated to the log position and term
        \/ Election_LeaderReady(n)

        \* Arrives here via the receipt of a NewLeadershipTerm message.
        \* Publishes replication/append position, replicates the log entries from the leader who sent
        \* us a NewLeadershipTerm message up to the next term, heads back to CANVASS once complete.
        \* Continues "looping" to replicate until within the current term, at which point a subsequent
        \* NewLeadershipTerm message will trigger a transition to FOLLOWER_REPLAY.
        \/ Election_FollowerLogReplication(n)

        \* Arrives here via the receipt of a NewLeadershipTerm message.
        \* Replays the local log to process leadership terms,
        \* upon completion, it will transition to either FOLLOWER_CATCHUP_INIT, FOLLOWER_LOG_INIT,
        \* or CANVASS, depending on whether we've fully caught up with the last known log position
        \* the leader sent.
        \/ Election_FollowerReplay(n)

        \* Sends a CatchupPosition message to the leader, then transitions to FOLLOWER_CATCHUP_AWAIT,
        \* waiting for the leader to start replaying its log. Can timeout and transition back to INIT.
        \/ Election_FollowerCatchupInit(n)

        \* Waits for the leader to start replaying its log, then transitions to FOLLOWER_CATCHUP;
        \* unless the logPosition and replay join position do not agree, or there is a timeout,
        \* in which case it transitions back to INIT.
        \/ Election_FollowerCatchupAwait(n)

        \* Polls the replay from the leader, sends append position periodically,
        \* updates commit position, transitions to FOLLOWER_LOG_INIT once the replayed position reaches
        \* the maximum known log position of a leader from a NewLeadershipTerm message. Can time out
        \* and transition back to INIT if no progress is made.
        \/ Election_FollowerCatchup(n)

        \* Transitions to FOLLOWER_READY if the live log subscription is already established;
        \* otherwise, it creates the subscription and waits for it to become connected via
        \* FOLLOWER_LOG_AWAIT.
        \/ Election_FollowerLogInit(n)

        \* Waits for the live log subscription to become connected, which isn't modelled here.
        \* Updates the recording log and logLeadershipTermId, then transitions to FOLLOWER_READY.
        \* Can time out and transition back to INIT if the subscription fails to connect.
        \/ Election_FollowerLogAwait(n)

        \* Sends an AppendPosition message to the leader to indicate we're ready, then transitions
        \* to CLOSED and completes the election. Can time out and transition back to INIT if unable
        \* to send the message.
        \/ Election_FollowerReady(n)

        \* Node performs consensus work when not in an election. On the leader, the node might
        \* append to the log, or publish its commit position. On a follower, node will replay the
        \* replicated log up to the notifiedCommitPosition, or it might enter an election on a timeout.
        \/ CM_ConsensusWork(n)

        \/ \E src \in Nodes \ {n}:
            \* Node receives an AppendPosition message and updates the "follower's" positions if its
            \* leadership term is less-than-or-equal-to the election's leadership term.
            \* Note that there is no LEADER check.
            \/ Adapter_OnAppendPosition(src, n)

            \* Node receives a CanvassPosition message and, if it is the leader, responds with a
            \* NewLeadershipTerm message containing the information for the next term after the
            \* message's logLeadershipTerm.
            \/ Adapter_OnCanvassPosition(src, n)

            \* Node receives a CatchupPosition message and, if it is the leader, starts a catchup replay
            \* for the follower.
            \/ Adapter_OnCatchupPosition(src, n)

            \* Node receives a CommitPosition message and updates its notified commit position
            \* if the message is from the currently "accepted" leader, or reverts to INIT if
            \* the message is from a new leader with a higher term.
            \/ Adapter_OnCommitPosition(src, n)

            \* Node receives a NewLeadershipTerm message and enters an election if the term is higher than
            \* its current term. If already in an election, it updates its election state with the
            \* information from the message, and may transition to INIT, CANVASS, FOLLOWER_REPLAY, or
            \* FOLLOWER_LOG_REPLICATION. It is worth noting the node may also truncate its log if the
            \* new leadership term's log position is behind the node's current append position.
            \/ Adapter_OnNewLeadershipTerm(src, n)

            \* Node receives a RequestVote message and decides whether to vote for the candidate or not
            \* depending on the candidate's candidate term and log position. Enters FOLLOWER_BALLOT if it
            \* votes for the candidate. When not in an election, receiving a RequestVote message with a
            \* higher candidate term causes the node to enter an election.
            \/ Adapter_OnRequestVote(src, n)

            \* Node receives a Vote message and if in the CANDIDATE_BALLOT state and the message matches
            \* the candidate term, it updates the vote and log information for the sender of the message.
            \/ Adapter_OnVote(src, n)

\*            \/ MessageLoss(src, dest)
            \* Perturbations to add later:
            \*  - Node restart (keeping persistent data only)

            \* Safety invariants to add:
            \*  - No log disagreements up to the commit position on each node
            \*  - Only one leader per term
            \*  - Commited entries must reside on a quorum of nodes

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
    /\ \A n, m \in Nodes : \/ network[n, m] = Null
                           \/ network[n, m].type \in MessageTypes

\* Invariant for debugging that will be falsified when replication works to some extent.
HasReplicated ==
    /\ \A n \in Nodes: commitPosition[n] > 0
    /\ \A n1, n2 \in Nodes:
        LET minCommitPos == Min({commitPosition[n1], commitPosition[n2]}) IN
        SubSeq(log[n1], 1, minCommitPos) = SubSeq(log[n2], 1, minCommitPos)

Debug_Replication == ~HasReplicated

\* Invariant for debugging that will be falsified when the election is completed on all nodes.
Debug_CompleteElection ==
    ~ /\ HasReplicated
      /\ \A n \in Nodes : election_state[n] = "CLOSED"

\* Invariant for debugging that will be falsified when a subsequent election is started and a node progresses to leader.
Debug_StartAnotherElection ==
    ~ /\ HasReplicated
      /\ Cardinality({n \in Nodes : /\ election_state[n] /= "CLOSED"
                                    /\ election_leaderMember[n] = Null}) >= QuorumSize

\* Invariant for debugging that will be falsified when a subsequent election is started and a node progresses
\* to become a candidate.
Debug_AnotherCandidate ==
    ~ /\ HasReplicated
      /\ \E n \in Nodes : role[n] = "CANDIDATE"

\* Invariant for debugging that will be falsified when a subsequent election is started and another node progresses
\* to leader (which is fine for different terms).
Debug_AnotherLeader ==
    ~ /\ HasReplicated
      /\ Cardinality({n \in Nodes : role[n] = "LEADER"}) >= 2

\* Invariant for debugging that will be falsified when multiple elections have completed on all nodes.
Debug_CompleteMultipleElections ==
    ~ \E n \in Nodes : \* /\ election_state[n] = "CLOSED"
                       /\ commitPosition[n] >= 2
                       /\ leadershipTermId[n] >= 1
                       /\ Len(SelectSeq(log[n], LAMBDA entry: entry.type = "NewLeadershipTerm")) >= 2

LogConsistency ==
    \A n1, n2 \in Nodes:
        LET minCommitPos == Min({commitPosition[n1], commitPosition[n2]}) IN
        SubSeq(log[n1], 1, minCommitPos) = SubSeq(log[n2], 1, minCommitPos)

=============================================================================

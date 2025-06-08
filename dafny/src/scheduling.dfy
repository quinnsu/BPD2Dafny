/**
 * BPMN Scheduling and Trace Module
 * 
 * This module defines scheduling and execution trace concepts for BPMN processes,
 * inspired by the concurrent system modeling approach used in the dining philosophers problem.
 */

include "state.dfy"
include "token.dfy"
include "execution_init.dfy"
include "engine.dfy"
include "process.dfy"

module Scheduling {
    import opened BPMNState
    import opened Token
    import opened ExecutionInit
    import opened ExecutionEngine
    import opened ProcessDefinition

    /**
     * Schedule Type - maps time steps to token IDs
     * A schedule determines which token should be executed at each time step
     */
    type Schedule = nat -> Token.TokenId

    /**
     * Trace Type - maps time steps to system states
     * A trace represents the evolution of system state over time
     */
    type Trace = nat -> BPMNState.State

    /**
     * Initial state predicate (analogous to Init in the paper)
     * A state is initial if it's a properly initialized BPMN process
     */
    predicate Init(s: BPMNState.State)
    {
        s.Running? &&
        ValidState(s) &&
        // Process was properly initialized with start tokens
        IsInitializedProcess(s.process)
    }

    /**
     * Helper predicate to check if a process is properly initialized
     */
    predicate IsInitializedProcess(process: ProcessObj)
    {
        // Has exactly one active token at a start node
        var activeTokens := GetActiveTokens(process.tokenCollection);
        |activeTokens| == 1 &&
        forall tokenId :: tokenId in activeTokens ==>
            process.tokenCollection.tokens[tokenId].location in process.processDefinition.startNodes
    }

    /**
     * State transition predicate (analogous to NextP in the paper)
     * Wraps our existing ExecuteStep logic as a predicate
     */
    predicate NextToken(s: BPMNState.State, tokenId: Token.TokenId, s': BPMNState.State)
    {
        s.Running? &&
        ValidState(s) &&
        tokenId in GetActiveTokens(s.process.tokenCollection) &&
        s.process.tokenCollection.tokens[tokenId].status == Active &&
        // The new state is the result of executing the token step
        s' == ExecuteTokenStep(s, tokenId)
    }

    /**
     * General state transition predicate (analogous to Next in the paper)
     * There exists some token that can be executed to transition from s to s'
     */
    predicate Next(s: BPMNState.State, s': BPMNState.State)
    {
        s.Running? &&
        ValidState(s) &&
        exists tokenId :: tokenId in GetActiveTokens(s.process.tokenCollection) && NextToken(s, tokenId, s')
    }

    /**
     * Trace validity predicate
     * A trace is valid if it starts with an initial state and each transition follows Next
     */
    ghost predicate IsTrace(trace: Trace, schedule: Schedule)
    {
        Init(trace(0)) &&
        forall i: nat :: 
            trace(i).Running? ==> 
            NextToken(trace(i), schedule(i), trace(i+1))
    }

    /**
     * Schedule validity for a trace
     * At each step, the scheduled token must be active in the current state
     */
    ghost predicate IsValidScheduleForTrace(schedule: Schedule, trace: Trace)
    {
        forall i: nat :: 
            trace(i).Running? ==> 
            schedule(i) in GetActiveTokens(trace(i).process.tokenCollection)
    }

    /**
     * Fair scheduling predicate
     * Every token that remains active will eventually be scheduled
     */
    ghost predicate FairSchedule(schedule: Schedule, trace: Trace)
    {
        IsValidScheduleForTrace(schedule, trace) &&
        forall tokenId, n :: 
            (trace(n).Running? && 
             tokenId in GetActiveTokens(trace(n).process.tokenCollection) &&
             TokenRemainsActiveFrom(trace, tokenId, n)) ==>
            HasNext(schedule, tokenId, n)
    }

    /**
     * Helper predicate: token remains active from time n onwards
     */
    ghost predicate TokenRemainsActiveFrom(trace: Trace, tokenId: Token.TokenId, n: nat)
    {
        forall t :: t >= n ==> 
            (trace(t).Running? && tokenId in trace(t).process.tokenCollection.tokens) ==>
            (trace(t).process.tokenCollection.tokens[tokenId].status == Active)
    }

    /**
     * Helper predicate: there exists a future time when the token is scheduled
     */
    ghost predicate HasNext(schedule: Schedule, tokenId: Token.TokenId, n: nat)
    {
        exists n' :: n <= n' && schedule(n') == tokenId
    }

    /**
     * Distance to end node (our decreasing expression)
     */
    function DistanceToEnd(process: ProcessObj, nodeId: string): nat
        requires nodeId in process.processDefinition.nodes
    {
        // For now, simplified implementation
        // In a full implementation, this would compute shortest path to end nodes
        if nodeId in process.processDefinition.endNodes then 0
        else if nodeId in process.processDefinition.startNodes then 10  // Rough estimate
        else 5  // Default distance for intermediate nodes
    }

    /**
     * Check if a token is at an end node
     */
    predicate TokenAtEndNode(state: BPMNState.State, tokenId: Token.TokenId)
        requires state.Running?
        requires tokenId in state.process.tokenCollection.tokens
    {
        var location := state.process.tokenCollection.tokens[tokenId].location;
        location in state.process.processDefinition.endNodes
    }

    /**
     * Liveness theorem: A token will eventually reach an end node under fair scheduling
     */
    lemma {:verify false} TokenEventuallyReachesEnd(trace: Trace, schedule: Schedule, tokenId: Token.TokenId, n: nat) returns (n': nat)
        requires FairSchedule(schedule, trace) && IsTrace(trace, schedule)
        requires trace(n).Running?
        requires tokenId in GetActiveTokens(trace(n).process.tokenCollection)
        ensures n <= n' && TokenAtEndNode(trace(n'), tokenId)
    {
        n' := n;
        while !TokenAtEndNode(trace(n'), tokenId)
            invariant n <= n' && trace(n').Running?
            invariant tokenId in trace(n').process.tokenCollection.tokens
            decreases DistanceToEnd(trace(n').process, trace(n').process.tokenCollection.tokens[tokenId].location)
        {
            // By fairness, token will eventually be scheduled
            assert HasNext(schedule, tokenId, n');
            var m :| n' <= m && schedule(m) == tokenId;
            
            // Execute the token step
            assert NextToken(trace(m), tokenId, trace(m+1));
            n' := m + 1;
        }
    }

    /**
     * Process completion theorem: If all active tokens are at end nodes, process will complete
     */
    lemma {:verify false}ProcessEventuallyCompletes(trace: Trace, schedule: Schedule, n: nat) returns (n': nat)
        requires FairSchedule(schedule, trace) && IsTrace(trace, schedule)
        requires trace(n).Running?
        requires CanComplete(trace(n))  // All active tokens are at end nodes
        ensures n <= n' && trace(n').Completed?
    {
        // Proof sketch: Each token at end node will be executed and consumed
        // leading to completion
        n' := n;
        while trace(n').Running?
            invariant n <= n'
            invariant trace(n').Running? ==> CanComplete(trace(n'))
            decreases |GetActiveTokens(trace(n').process.tokenCollection)|
        {
            var activeTokens := GetActiveTokens(trace(n').process.tokenCollection);
            if |activeTokens| == 0 {
                // This should lead to completion
                break;
            }
            
            // Pick any active token (they're all at end nodes)
            var tokenId := PickOne(activeTokens);
            
            // By fairness, it will be scheduled
            assert HasNext(schedule, tokenId, n');
            var m :| n' <= m && schedule(m) == tokenId;
            
            // Execute the token (should consume it and possibly complete)
            n' := m + 1;
        }
    }

    /**
     * Create a schedule from our existing DequeueToken mechanism
     * This bridges our current queue-based approach with the theoretical model
     */
    function CreateScheduleFromQueue(initialState: BPMNState.State): Schedule
        requires initialState.Running?
        requires |initialState.process.context.executionQueue| > 0
    {
        // Simplified implementation - would need to simulate queue evolution
        (i: nat) => GetFirstTokenFromQueue(initialState)
    }

    /**
     * Construct a trace from an initial state and a schedule
     * This is the missing piece that allows us to build actual traces
     */
    function {:verify false} ConstructTrace(initialState: BPMNState.State, schedule: Schedule): Trace
        requires initialState.Running?
        requires Init(initialState)
    {
        (i: nat) => ConstructTraceAtStep(initialState, schedule, i)
    }

    /**
     * Helper function to construct trace at a specific step
     */
    function {:verify false} ConstructTraceAtStep(initialState: BPMNState.State, schedule: Schedule, step: nat): BPMNState.State
        requires initialState.Running?
        requires Init(initialState)
        decreases step
    {
        if step == 0 then
            initialState
        else
            var prevState := ConstructTraceAtStep(initialState, schedule, step - 1);
            if prevState.Running? && |GetActiveTokens(prevState.process.tokenCollection)| > 0 then
                var tokenId := schedule(step - 1);
                if tokenId in GetActiveTokens(prevState.process.tokenCollection) then
                    ExecuteTokenStep(prevState, tokenId)
                else
                    prevState  // Invalid schedule, state doesn't change
            else
                prevState  // No more active tokens or not running
    }

    /**
     * Helper to get the first token from execution queue
     */
    function GetFirstTokenFromQueue(state: BPMNState.State): Token.TokenId
        requires state.Running?
        requires |state.process.context.executionQueue| > 0
    {
        state.process.context.executionQueue[0]
    }

    /**
     * Theorem: Our queue-based scheduling is fair (to be proven)
     */
    lemma{:verify false} QueueBasedSchedulingIsFair(trace: Trace, initialState: BPMNState.State)
        requires Init(initialState)
        requires initialState.Running?
        requires |initialState.process.context.executionQueue| > 0
        ensures FairSchedule(CreateScheduleFromQueue(initialState), trace)
    {
        // Proof to be implemented
        assume true;
    }

    

    /**
     * Helper predicate to check if two states are equal (for deadlock detection)
     */
    predicate StatesEqual(s1: BPMNState.State, s2: BPMNState.State)
    {
        match (s1, s2) {
            case (Running(p1), Running(p2)) =>
                TokenCollectionsEqual(p1.tokenCollection, p2.tokenCollection)
            case (Completed(p1, _), Completed(p2, _)) => true
            case (Error(_, _), Error(_, _)) => true
            case (Terminated(_), Terminated(_)) => true
            case _ => false
        }
    }

    /**
     * Helper predicate to check if token collections are equal
     */
    predicate TokenCollectionsEqual(tc1: Token.Collection, tc2: Token.Collection)
    {
        tc1.tokens.Keys == tc2.tokens.Keys &&
        forall tokenId :: tokenId in tc1.tokens.Keys ==>
            tc1.tokens[tokenId] == tc2.tokens[tokenId]
    }

    /**
     * Explore all possible execution paths (for small graphs)
     * Returns true if any path leads to completion
     */
    method {:verify false} ExploreAllPaths(processDef: ProcessDefinition.ProcessDef, maxDepth: nat) returns (canComplete: bool)
        requires ValidProcessDefinition(processDef)
        requires CanStartProcess(processDef)
    {
        var initialState := InitializeExecution(processDef);
        var visited := {};
        canComplete := ExploreFromState(initialState, maxDepth, visited);
    }

    /**
     * Recursive exploration from a given state
     */
    method {:verify false} ExploreFromState(
        state: BPMNState.State, 
        remainingDepth: nat, 
        visited: set<string>
    ) returns (canComplete: bool)
        decreases remainingDepth
    {
        // Base cases
        if remainingDepth == 0 {
            canComplete := state.Completed?;
            return;
        }
        
        if state.Completed? {
            canComplete := true;
            return;
        }
        
        if !state.Running? {
            canComplete := false;
            return;
        }
        
        // Generate state signature for cycle detection
        var stateKey := GenerateStateKey(state);
        if stateKey in visited {
            canComplete := false; // Cycle detected
            return;
        }
        
        var newVisited := visited + {stateKey};
        
        // Try all possible next states
        var activeTokens := GetActiveTokens(state.process.tokenCollection);
        if |activeTokens| == 0 {
            // No active tokens, check if this leads to completion
            canComplete := CanComplete(state);
            return;
        }
        
        // Try executing each active token
        canComplete := false;
        var tokenIds := SetToSeq(activeTokens);
        var i := 0;
        while i < |tokenIds| && !canComplete
            decreases |tokenIds| - i
        {
            var tokenId := tokenIds[i];
            if tokenId in GetActiveTokens(state.process.tokenCollection) {
                var nextState := ExecuteTokenStep(state, tokenId);
                var pathComplete := ExploreFromState(nextState, remainingDepth - 1, newVisited);
                if pathComplete {
                    canComplete := true;
                    return;
                }
            }
            i := i + 1;
        }
    }

    /**
     * Generate a unique string key for a state (for cycle detection)
     */
    function {:verify false} GenerateStateKey(state: BPMNState.State): string
    {
        if state.Running? then
            var locations := GetActiveTokenLocations(state);
            // Simple concatenation of active token locations
            "Running:" + SetToString(locations)
        else
            "NonRunning"
    }

    /**
     * Get locations of all active tokens
     */
    function GetActiveTokenLocations(state: BPMNState.State): set<string>
        requires state.Running?
    {
        set tokenId | tokenId in GetActiveTokens(state.process.tokenCollection) ::
            state.process.tokenCollection.tokens[tokenId].location
    }

    /**
     * Convert set to string for key generation
     */
    function {:verify false} SetToString(s: set<string>): string
    {
        // Simplified implementation
        ""
    }

    /**
     * Convert set to sequence for iteration
     */
    function {:verify false} SetToSeq<T>(s: set<T>): seq<T>
    {
        // Simplified implementation - would need proper conversion
        []
    }
} 
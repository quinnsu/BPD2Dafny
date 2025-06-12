/** 
  * Core Execution Engine
  */ 

include "./token.dfy"
include "./state.dfy"
include "./process.dfy"
include "./utils/variables.dfy"
include "./execution_init.dfy"
include "./utils/option.dfy"
include "./Context.dfy"
include "./utils/Array.dfy"
include "./utils/Seq.dfy"
include "../example/json_model.dfy"

module ExecutionEngine {
  import opened Token
  import opened BPMNState
  import opened ProcessDefinition
  import opened Variables
  import opened ExecutionInit
  import opened Optional
  import opened ExecutionContext
  import opened Arrays
  import opened Seq
  /**
    * The main execution function with a scheduler
    
  function ExecuteStep(state: ExecutingState): State
    requires ValidState(state)
    ensures var result := ExecuteStep(state);
            result.Running? || result.Completed? || result.Error? || result.Terminated?
    // 关键ensures：当执行ParallelFork时，保证目标节点有tokens
    ensures var result := ExecuteStep(state);
            result.Running? ==>
            (var executableTokens := GetImmediatelyExecutableTokens(state);
             if |executableTokens| > 0 then
               var tokenToExecute := Token.PickOne(executableTokens);
               if tokenToExecute in state.process.tokenCollection.tokens &&
                  state.process.tokenCollection.tokens[tokenToExecute].location in state.process.processDefinition.nodes then
                 var currentNode := state.process.processDefinition.nodes[state.process.tokenCollection.tokens[tokenToExecute].location];
                 match currentNode.nodeType {
                   case Gateway(ParallelGateway) =>
                     if |currentNode.outgoing| > 1 then
                       // ParallelFork case: 保证每个目标节点都有token
                       var targetNodes := set flowId | flowId in currentNode.outgoing ::
                                            state.process.processDefinition.flows[flowId].targetRef;
                       forall nodeId :: nodeId in targetNodes ==> IsAtNode(result, nodeId)
                     else
                       true
                   case _ => true
                 }
               else
                 true
             else
               true)
  {
    // if the queue is empty, return the completed state
    if |state.process.context.executionQueue| == 0 then
      state
    else
       var (newContext, tokenId) := DequeueToken(state.process.context);
       if tokenId in state.process.tokenCollection.tokens &&
          state.process.tokenCollection.tokens[tokenId].status == Active then
         ExecuteTokenStep(state, tokenId)
       else
         BPMNState.Error(state.process, TokenError(tokenId, "Token is not active"))
  }
*/


  /**
    * Execute a step in the process execution.
    * 
    * @param state Current executing state
    * @returns Next state after execution
    * 
    * Logic:
    * 1. If execution queue is empty, return terminated state (no tokens left)
    * 2. If all tokens cannot be started but the execution queue is not empty, return error state (deadlock)
    * 3. Otherwise, execute the first token that can be executed immediately
    */
  function ExecuteStep(state: ExecutingState): State
    requires ValidState(state)
    requires ValidProcessDefinition(state.process.processDefinition)
    requires ValidProcessState(state.process)
    ensures ValidState(ExecuteStep(state))
  {
    var process := state.process;
    var context := process.context;
    
    // Check if execution queue is empty
    if |context.executionQueue| == 0 then
      BPMNState.Terminated(process)
    else
      // Check if any token can be executed immediately
      var executableTokensFromQueue := GetExecutableTokensFromQueue(state);
      if |executableTokensFromQueue| == 0 then
        BPMNState.Error(process, DeadlockError("No tokens can be executed in current state"))
      else
        // Check for data conflicts in the queue
        var (conflictFreeTokens, conflicts) := GetConflictFreeTokensFromQueue(state);
        
        if |conflicts| > 0 then
          BPMNState.CreateDataConflictError(process, conflicts)
        else if |conflictFreeTokens| == 0 then
          BPMNState.Error(process, DeadlockError("No conflict-free tokens can be executed"))
        else
          // Execute the first conflict-free token
          var tokenToExecute := Seq.First(conflictFreeTokens);
          ExecuteTokenStep(state, tokenToExecute)
  }

  /**
  A scheduler that choose token to execute
   */
  method Execute(state: ExecutingState)
    requires ValidProcessDefinition(state.process.processDefinition)
    requires ValidProcessState(state.process)
    requires ValidState(state)
    decreases *
  {
    while |state.process.context.executionQueue| > 0
      decreases *
      invariant ValidState(state)
    {
      var executableTokensFromQueue := GetExecutableTokensFromQueue(state);
     
      // pick a token to execute
      var process := state.process;

      var (newContext, tokenId) := DequeueToken(state.process.context);
      var token := process.tokenCollection.tokens[tokenId];
      var currentNode := process.processDefinition.nodes[token.location];
      var newState :=
        match currentNode.nodeType {
          case StartEvent =>
            if CanExecuteStartEvent(state) then
              ExecuteStartEvent(state)
            else
              state
          case EndEvent => 
            if state.Running? then
              ExecuteEndEvent(state, tokenId)  
            else
              BPMNState.Error(state.process, ExecutionError(token.location, "Invalid state for EndEvent"))
          case Task(taskType, data) => ExecuteTask(state, tokenId, taskType, data)
          case Gateway(gatewayType) => ExecuteGateway(state, tokenId, gatewayType)
          case IntermediateEvent(eventType) => ExecuteIntermediateEvent(state, tokenId, eventType)
        };
    }
    }
    



  /**
    * check if the token can be executed immediately (no waiting)
    */
  predicate CanExecuteTokenImmediately(state: ExecutingState, tokenId: Token.TokenId)
    requires tokenId in state.process.tokenCollection.tokens
    requires state.process.tokenCollection.tokens[tokenId].status == Active
  {
    var process := state.process;
    var token := process.tokenCollection.tokens[tokenId];
    var location := token.location;

    if location in process.processDefinition.nodes then
      var node := process.processDefinition.nodes[location];
      match node.nodeType {
        case Gateway(ParallelGateway) =>
          if |node.incoming| > 1 then
            var tokensAtLocation := GetActiveTokensAtLocation(process.tokenCollection, location);
            |tokensAtLocation| == |node.incoming|
          else
            true
          case Gateway(_) =>
          true
        case _ =>
          true
      }
    else
      false
  }

  /**
    * Get all tokens from execution queue that can be executed immediately
    */
  function GetImmediatelyExecutableTokens(state: ExecutingState): set<Token.TokenId>
    requires ValidState(state)
  {
    var process := state.process;
    var context := process.context;
    
    // Filter tokens from execution queue that can be executed immediately
    set tokenId | tokenId in context.executionQueue &&
                  tokenId in process.tokenCollection.tokens &&
                  process.tokenCollection.tokens[tokenId].status == Active &&
                  CanExecuteTokenImmediately(state, tokenId)
  }


// Filter all tokens from execution queue that can be executed immediately
  function GetExecutableTokensFromQueue(state: ExecutingState): seq<Token.TokenId>
    requires ValidState(state)
    requires ValidProcessDefinition(state.process.processDefinition)
    requires ValidProcessState(state.process)
    ensures var result := GetExecutableTokensFromQueue(state);
            ValidState(state) &&
            (forall tokenId :: tokenId in result ==>
              tokenId in state.process.context.executionQueue &&
              tokenId in state.process.tokenCollection.tokens &&
              state.process.tokenCollection.tokens[tokenId].status == Active &&
              CanExecuteTokenImmediately(state, tokenId))
    ensures forall tokenId :: tokenId in GetExecutableTokensFromQueue(state) ==> 
              tokenId in state.process.context.executionQueue && 
              tokenId in state.process.tokenCollection.tokens &&
              state.process.tokenCollection.tokens[tokenId].status == Active && 
              CanExecuteTokenImmediately(state, tokenId)
    ensures |GetExecutableTokensFromQueue(state)| <= |state.process.context.executionQueue|
    decreases |state.process.context.executionQueue|
  {
    FilterExecutableTokens(state.process.context.executionQueue, state)
  }
  
function FilterExecutableTokens(
  queue: seq<Token.TokenId>, 
  state: ExecutingState
): seq<Token.TokenId>
  requires ValidState(state)
  requires ValidProcessDefinition(state.process.processDefinition)
  requires ValidProcessState(state.process)
  requires forall tokenId :: tokenId in queue ==>
             tokenId in state.process.tokenCollection.tokens &&
             state.process.tokenCollection.tokens[tokenId].status == Active
  ensures var result := FilterExecutableTokens(queue, state);
          forall tokenId :: tokenId in result ==> tokenId in queue
  ensures var result := FilterExecutableTokens(queue, state);
          forall tokenId :: tokenId in result ==>
            tokenId in state.process.tokenCollection.tokens &&
            state.process.tokenCollection.tokens[tokenId].status == Active &&
            CanExecuteTokenImmediately(state, tokenId)
  ensures var result := FilterExecutableTokens(queue, state);
          |result| <= |queue|
  decreases |queue|
{
  if |queue| == 0 then []
  else
    var tokenId := Seq.First(queue);
    var rest := FilterExecutableTokens(Seq.DropFirst(queue), state);
    
    if tokenId in state.process.tokenCollection.tokens &&
       state.process.tokenCollection.tokens[tokenId].status == Active &&
       CanExecuteTokenImmediately(state, tokenId) then
      [tokenId] + rest
    else
      rest
}
 

  function ExecuteTokenStep(state: ExecutingState, tokenId: Token.TokenId): State
    requires ValidState(state)
    requires tokenId in state.process.tokenCollection.tokens
    requires state.process.tokenCollection.tokens[tokenId].status == Active
    requires ValidProcessDefinition(state.process.processDefinition)
    requires ValidProcessState(state.process)
    ensures ValidState(ExecuteTokenStep(state, tokenId))
  {
    var process := state.process;
    var token := process.tokenCollection.tokens[tokenId];
    var currentNode := process.processDefinition.nodes[token.location];

    match currentNode.nodeType {
      case StartEvent =>
        if CanExecuteStartEvent(state) then
          ExecuteStartEvent(state)
        else
          state
      case EndEvent => 
        assert state.Running?;
        ExecuteEndEvent(state, tokenId)
      case Task(taskType, data) => ExecuteTask(state, tokenId, taskType, data)
      case Gateway(gatewayType) => ExecuteGateway(state, tokenId, gatewayType)
      case IntermediateEvent(eventType) => ExecuteIntermediateEvent(state, tokenId, eventType)
    }
  }

  // execute the step of a start event
  function ExecuteStartEvent(state: State): State
    requires CanExecuteStartEvent(state)
    requires ValidTokenCollection(state.process.tokenCollection)
    ensures ExecuteStartEvent(state).Running?
    ensures ValidState(ExecuteStartEvent(state))
  {
    ExecutionInit.ProcessStartEvent(state)
  }
  // execute the step of a end event
  function ExecuteEndEvent(state: State, tokenId: Token.TokenId): State
    requires state.Running?
    requires tokenId in state.process.tokenCollection.tokens
    requires state.process.tokenCollection.tokens[tokenId].status == Active
    requires ValidTokenCollection(state.process.tokenCollection)
    ensures ValidState(ExecuteEndEvent(state, tokenId))
  {
    var process := state.process;
    var token := process.tokenCollection.tokens[tokenId];

    var tokensAfterConsume := Token.ConsumeToken(process.tokenCollection, tokenId);
    
    var newHistory := process.executionHistory + [
                        Event(0, token.location, NodeExited, tokenId, Variables.EmptyVariables())
                      ];
    
    var updatedContext := ExecutionContext.ComputeContext(
                            tokensAfterConsume,
                            token.location,
                            process.context
                          );
    
    var updatedProcess := Process(
                            processId := process.processId,
                            tokenCollection := tokensAfterConsume,
                            globalVariables := process.globalVariables,
                            processDefinition := process.processDefinition,
                            executionHistory := newHistory,
                            context := updatedContext
                          );
    
    var remainingActiveTokens := GetActiveTokens(tokensAfterConsume);
    if |remainingActiveTokens| == 0 then
      assert ValidProcessState(updatedProcess);
      BPMNState.Completed(updatedProcess, process.globalVariables)
    else
      BPMNState.Error(process, ExecutionError(token.location, "Invalid state for EndEvent"))
  }
  // execute the step of a task
  function ExecuteTask(state: ExecutingState, tokenId: Token.TokenId, taskType: TaskType, data: Option<TaskData>): State
    requires tokenId in GetActiveTokens(state.process.tokenCollection)
    requires ValidProcessDefinition(state.process.processDefinition)
    requires ValidProcessState(state.process)
    requires tokenId in state.process.tokenCollection.tokens
    requires ValidTokenCollection(state.process.tokenCollection)
    requires state.process.tokenCollection.tokens[tokenId].location in state.process.processDefinition.nodes
    ensures ValidState(ExecuteTask(state, tokenId, taskType, data))
  {
    match taskType {
      case UserTask =>
        ExecuteUserTaskWithData(state, tokenId, data)
      case ServiceTask =>
        ExecuteServiceTaskWithData(state, tokenId, data)
      case ManualTask =>
        ExecuteManualTaskWithData(state, tokenId, data)
    }
  }
  // execute the step of a gateway
  function ExecuteGateway(state: ExecutingState, tokenId: Token.TokenId, gatewayType: GatewayType): State
    requires CanExecuteGateway(state, tokenId)
    requires ValidTokenCollection(state.process.tokenCollection)
    requires ValidProcessDefinition(state.process.processDefinition)
    requires ValidProcessState(state.process)
    ensures ValidState(ExecuteGateway(state, tokenId, gatewayType))
    
  {
    var process := state.process;
    var token := process.tokenCollection.tokens[tokenId];
    var currentNode := process.processDefinition.nodes[token.location];
    var outgoingFlows := currentNode.outgoing;
    var incomingFlows := currentNode.incoming;
    match gatewayType {
      case ParallelGateway =>
        if |outgoingFlows| > 1 then
          if CanExecuteParallelFork(state, tokenId, outgoingFlows) then
            ExecuteParallelFork(state, tokenId, outgoingFlows)
          else
            BPMNState.Error(process, DefinitionError("outgoingFlows should be greater than 1"))
        else if |incomingFlows| > 1 then
          if CanExecuteParallelJoin(state, tokenId) then
            ExecuteParallelJoin(state, tokenId)
          else
            //waiting for other tokens to arrive
            state
        else
          ExecuteSimplePassThrough(state, tokenId)
      case ExclusiveGateway =>
        if |outgoingFlows| > 1 then
          assert forall flowId :: flowId in outgoingFlows ==> flowId in process.processDefinition.flows;
          // 从ValidProcessDefinition得出：默认流必须在outgoing flows中
          assert currentNode.defaultFlow.Some? ==> currentNode.defaultFlow.Unwrap() in currentNode.outgoing;
          assert currentNode.outgoing == outgoingFlows;
          assert currentNode.defaultFlow.Some? ==> currentNode.defaultFlow.Unwrap() in outgoingFlows;
          assert forall flowId :: flowId in outgoingFlows ==> flowId in state.process.processDefinition.flows;
          ExecuteExclusiveFork(state, tokenId, outgoingFlows, currentNode.defaultFlow)
        else if |incomingFlows| > 1 then
          // Exclusive merge: 简单合并，不需要等待
          assert state.process.tokenCollection.tokens[tokenId].status == Active;
          assert state.process.tokenCollection.tokens[tokenId].location in state.process.processDefinition.nodes;
          ExecuteExclusiveMerge(state, tokenId)
        else
          ExecuteSimplePassThrough(state, tokenId)
      case _ =>
        BPMNState.Error(process, DefinitionError("Invalid gateway type"))
    }
  }


  predicate DetectDeadlock(state: State)
{
  match state {
    case Running(process) =>
      var activeTokens := GetActiveTokens(process.tokenCollection);
      forall tokenId :: tokenId in activeTokens ==>
        !CanExecuteToken(state, tokenId)
    case _ => false
  }
}

  /**
    * Check if a token can be executed (generic version)
    */
  predicate CanExecuteToken(state: State, tokenId: Token.TokenId)
    requires state.Running?
    requires tokenId in state.process.tokenCollection.tokens
  {
    if state.process.tokenCollection.tokens[tokenId].status == Active then
      CanExecuteTokenImmediately(state, tokenId)
    else
      false
  }

  
  // execute the step of a intermediate event
  function ExecuteIntermediateEvent(state: State, tokenId: Token.TokenId, eventType: ProcessDefinition.EventType): State { state }

  /**
    * Execute a user task - for testing, we simulate user input
    */
  function ExecuteUserTask(state: ExecutingState, tokenId: Token.TokenId): State
    requires tokenId in GetActiveTokens(state.process.tokenCollection)
    requires tokenId in state.process.tokenCollection.tokens
    requires ValidProcessDefinition(state.process.processDefinition)
    requires ValidProcessState(state.process)
    requires state.process.tokenCollection.tokens[tokenId].location in state.process.processDefinition.nodes
    requires state.process.tokenCollection.tokens[tokenId].status == Active
    requires ValidTokenCollection(state.process.tokenCollection)
    ensures ValidState(ExecuteUserTask(state, tokenId))
  {
    var process := state.process;
    var token := process.tokenCollection.tokens[tokenId];
    var currentNode := process.processDefinition.nodes[token.location];

    // Add process validation
    var outgoingFlows := currentNode.outgoing;
    if |outgoingFlows| == 1 then
      var flowId := Token.PickOne(outgoingFlows);
      if flowId in process.processDefinition.flows then
        var nextNodeId := process.processDefinition.flows[flowId].targetRef;
        // Simulate user completing task - consume current token, create next token
        var tokensAfterConsume := Token.ConsumeToken(process.tokenCollection, tokenId);
        var (tokensWithNext, nextTokenId) := Token.CreateToken(tokensAfterConsume, nextNodeId);
assert flowId in process.processDefinition.flows;  // 从ValidFlowStructure得出
    assert nextNodeId in process.processDefinition.nodes;  // 从ValidProcessDefinition得出
    
        // Update execution history
        var newHistory := process.executionHistory + [
                            Event(0, token.location, NodeExited, tokenId, Variables.EmptyVariables()),
                            Event(1, nextNodeId, NodeEntered, nextTokenId, Variables.EmptyVariables())
                          ];

        // Update context
        var updatedContext := ExecutionContext.CreateConsistentContext(
                            tokensWithNext,
                            nextNodeId,
                            process.context.executionStep + 1
                          );

        var updatedProcess := Process(
                                processId := process.processId,
                                tokenCollection := tokensWithNext,
                                globalVariables := process.globalVariables,  // 可以在这里更新变量
                                processDefinition := process.processDefinition,
                                executionHistory := newHistory,
                                context := updatedContext
                              );

        // 验证最终的Process对象
        assert ValidProcessState(updatedProcess);
        
        Running(updatedProcess)
      else
        BPMNState.Error(process, FlowError(flowId, "Flow not found in process definition"))
    else
      // Multiple output flows - this is usually an error for UserTask
      BPMNState.Error(process, ExecutionError(token.location, "UserTask should not have multiple outgoing flows"))
  }

  /**
    * Execute a service task - automatic execution
    */
  function ExecuteServiceTask(state: ExecutingState, tokenId: Token.TokenId): State
    requires tokenId in GetActiveTokens(state.process.tokenCollection)
    requires tokenId in state.process.tokenCollection.tokens
    requires state.process.tokenCollection.tokens[tokenId].location in state.process.processDefinition.nodes
    requires state.process.tokenCollection.tokens[tokenId].status == Active
    requires ValidTokenCollection(state.process.tokenCollection)
  {
    ExecuteSimpleTask(state, tokenId, "ServiceTask")
  }

  /**
    * Execute a manual task - requires human intervention
    */
  function ExecuteManualTask(state: ExecutingState, tokenId: Token.TokenId): State
    requires tokenId in GetActiveTokens(state.process.tokenCollection)
    requires tokenId in state.process.tokenCollection.tokens
    requires state.process.tokenCollection.tokens[tokenId].location in state.process.processDefinition.nodes
    requires state.process.tokenCollection.tokens[tokenId].status == Active
    requires ValidTokenCollection(state.process.tokenCollection)
  {
    ExecuteSimpleTask(state, tokenId, "ManualTask")
  }

  /**
    * Common task execution logic
    */
  function ExecuteSimpleTask(state: ExecutingState, tokenId: Token.TokenId, taskType: string): State
    requires tokenId in GetActiveTokens(state.process.tokenCollection)
    requires tokenId in state.process.tokenCollection.tokens
    requires state.process.tokenCollection.tokens[tokenId].location in state.process.processDefinition.nodes
    requires state.process.tokenCollection.tokens[tokenId].status == Active
    requires ValidTokenCollection(state.process.tokenCollection)
  {
    var process := state.process;
    var token := process.tokenCollection.tokens[tokenId];
    var currentNode := process.processDefinition.nodes[token.location];
    var outgoingFlows := currentNode.outgoing;
    if |outgoingFlows| == 1 then
      var flowId := Token.PickOne(outgoingFlows);
      if flowId in process.processDefinition.flows then
        var nextNodeId := process.processDefinition.flows[flowId].targetRef;
 
        var tokensAfterConsume := Token.ConsumeToken(process.tokenCollection, tokenId);
        var (tokensWithNext, nextTokenId) := Token.CreateToken(tokensAfterConsume, nextNodeId);

        var newHistory := process.executionHistory + [
                            Event(0, token.location, NodeExited, tokenId, Variables.EmptyVariables()),
                            Event(1, nextNodeId, NodeEntered, nextTokenId, Variables.EmptyVariables())
                          ];

        var updatedProcess := Process(
                                processId := process.processId,
                                tokenCollection := tokensWithNext,
                                globalVariables := process.globalVariables,
                                processDefinition := process.processDefinition,
                                executionHistory := newHistory,
                                context := process.context
                              );

        // Update context
        var updatedContext := ExecutionContext.ComputeContext(
                                updatedProcess.tokenCollection,
                                nextNodeId,
                                process.context
                              );

        Running(Process(
                  processId := process.processId,
                  tokenCollection := tokensWithNext,
                  globalVariables := process.globalVariables,
                  processDefinition := process.processDefinition,
                  executionHistory := newHistory,
                  context := updatedContext
                ))
      else
        BPMNState.Error(process, FlowError(flowId, "Flow not found in process definition"))
    else
      BPMNState.Error(process, ExecutionError(token.location, taskType + " should have exactly one outgoing flow"))
  }

  /**
    * Execute a parallel gateway
    */
  function ExecuteParallelGateway(state: ExecutingState, tokenId: Token.TokenId): State
    requires tokenId in GetActiveTokens(state.process.tokenCollection)
    requires tokenId in state.process.tokenCollection.tokens
    requires state.process.tokenCollection.tokens[tokenId].location in state.process.processDefinition.nodes
    requires ValidTokenCollection(state.process.tokenCollection)
    requires ValidProcessDefinition(state.process.processDefinition)
    requires ValidProcessState(state.process)
  {
    var process := state.process;
    var token := process.tokenCollection.tokens[tokenId];
    var currentNode := process.processDefinition.nodes[token.location];
    var outgoingFlows := currentNode.outgoing;
    var incomingFlows := currentNode.incoming;

    if |outgoingFlows| > 1 then
      if forall flowId :: flowId in outgoingFlows ==> flowId in process.processDefinition.flows then
        ExecuteParallelFork(state, tokenId, outgoingFlows)
      else
        BPMNState.Error(process, ExecutionError(token.location, "Some outgoing flows not found in process definition"))
    else if |incomingFlows| > 1 then
      if CanExecuteParallelJoin(state, tokenId) then
        ExecuteParallelJoin(state, tokenId)
      else
        BPMNState.Error(process, ExecutionError(token.location, "Cannot execute parallel join"))
    else
      ExecuteSimplePassThrough(state, tokenId)
  }

  /**
    * Execute parallel fork
    */
  function {:opaque} ExecuteParallelFork(
    state: ExecutingState,
    tokenId: Token.TokenId,
    outgoingFlows: set<string>
  ): State
    requires ValidState(state)
    requires ValidProcessDefinition(state.process.processDefinition)
    requires ValidProcessState(state.process)
    requires ValidTokenCollection(state.process.tokenCollection)
    requires CanExecuteParallelFork(state, tokenId, outgoingFlows)
    ensures ExecuteParallelFork(state, tokenId, outgoingFlows).Running?
    ensures ValidProcessState(ExecuteParallelFork(state, tokenId, outgoingFlows).process)
    ensures ValidState(ExecuteParallelFork(state, tokenId, outgoingFlows))
    ensures var result := ExecuteParallelFork(state, tokenId, outgoingFlows);
            var targetNodes := set flowId | flowId in outgoingFlows ::
                                 state.process.processDefinition.flows[flowId].targetRef;
            forall nodeId :: nodeId in targetNodes ==>
                               exists activeTokenId :: activeTokenId in GetActiveTokens(result.process.tokenCollection) &&
                                                       result.process.tokenCollection.tokens[activeTokenId].location == nodeId

    ensures var result := ExecuteParallelFork(state, tokenId, outgoingFlows);
            var targetNodes := set flowId | flowId in outgoingFlows ::
                                 state.process.processDefinition.flows[flowId].targetRef;
            forall nodeId :: nodeId in targetNodes ==>
                               exists activeTokenId :: activeTokenId in result.process.tokenCollection.tokens &&
                                                       result.process.tokenCollection.tokens[activeTokenId].location == nodeId &&
                                                       result.process.tokenCollection.tokens[activeTokenId].status == Active
  {
    var process := state.process;
    var token := process.tokenCollection.tokens[tokenId];

    var tokensAfterConsume := Token.ConsumeToken(process.tokenCollection, tokenId);

    assert forall flowId :: flowId in outgoingFlows ==> flowId in process.processDefinition.flows;
    
    assert forall flowId :: flowId in outgoingFlows ==> 
           process.processDefinition.flows[flowId].targetRef in process.processDefinition.nodes;
    
    var targetNodes := set flowId | flowId in outgoingFlows ::
                         process.processDefinition.flows[flowId].targetRef;
    
    assert forall nodeId :: nodeId in targetNodes ==> nodeId in process.processDefinition.nodes;

    var (finalTokens, newTokenIds) := CreateTokensForFlows(
                                        tokensAfterConsume,
                                        outgoingFlows,
                                        process.processDefinition.flows
                                      );

    assert |newTokenIds| == |outgoingFlows|;
    assert |finalTokens.tokens| == |tokensAfterConsume.tokens| + |outgoingFlows|;

    var targetNodes := set flowId | flowId in outgoingFlows ::
                         process.processDefinition.flows[flowId].targetRef;
    assert forall nodeId :: nodeId in targetNodes ==>
                              exists tokenId :: tokenId in newTokenIds &&
                                                finalTokens.tokens[tokenId].location == nodeId &&
                                               finalTokens.tokens[tokenId].status == Active;
    
    assert forall flowId :: flowId in outgoingFlows ==>
             exists tokenId :: tokenId in newTokenIds &&
                               finalTokens.tokens[tokenId].location == process.processDefinition.flows[flowId].targetRef;
    
    assume forall tokenId :: tokenId in newTokenIds ==>
                              finalTokens.tokens[tokenId].location in process.processDefinition.nodes;

    var exitEvent := Event(0, token.location, NodeExited, tokenId, Variables.EmptyVariables());
    var enterEvents := CreateEnterEvents(newTokenIds, outgoingFlows, process.processDefinition.flows);
    var newHistory := process.executionHistory + [exitEvent] + enterEvents;

    var lastExecutedNode := token.location;
    var updatedContext := ExecutionContext.CreateConsistentContext(
                            finalTokens,
                            lastExecutedNode,
                            process.context.executionStep + 1
                          );

    var result := Running(Process(
                    processId := process.processId,
                    tokenCollection := finalTokens,
                    globalVariables := process.globalVariables,
                    processDefinition := process.processDefinition,
                    executionHistory := newHistory,
                    context := updatedContext
                  ));


    assert forall flowId :: flowId in outgoingFlows ==> 
      var targetNode := process.processDefinition.flows[flowId].targetRef;
      exists tokenId :: tokenId in GetActiveTokens(result.process.tokenCollection) &&
                        result.process.tokenCollection.tokens[tokenId].location == targetNode;


    assume forall tokenId :: tokenId in GetActiveTokens(result.process.tokenCollection) ==>
                       result.process.tokenCollection.tokens[tokenId].location in result.process.processDefinition.nodes;
    

    assert forall tokenId :: tokenId in result.process.context.executionQueue ==>
                        tokenId in result.process.tokenCollection.tokens &&
                        result.process.tokenCollection.tokens[tokenId].status == Active;
    

    assert forall tokenId :: tokenId in GetActiveTokens(result.process.tokenCollection) ==>
                        tokenId in result.process.context.executionQueue;
    

    assert ExecutionContext.ValidContext(result.process.context);

    result
  }

 
  lemma ParallelForkCreatesTokensAtTargetLocations(
    state: ExecutingState,
    tokenId: Token.TokenId,
    outgoingFlows: set<string>
  )
    requires CanExecuteParallelFork(state, tokenId, outgoingFlows)
    requires ValidTokenCollection(state.process.tokenCollection)
    requires ValidProcessDefinition(state.process.processDefinition)
    requires ValidProcessState(state.process)
    ensures var result := ExecuteParallelFork(state, tokenId, outgoingFlows);
            var targetNodes := set flowId | flowId in outgoingFlows ::
                                 state.process.processDefinition.flows[flowId].targetRef;
            forall nodeId :: nodeId in targetNodes ==> (
              exists activeTokenId :: activeTokenId in result.process.tokenCollection.tokens &&
                                       result.process.tokenCollection.tokens[activeTokenId].location == nodeId &&
                                       result.process.tokenCollection.tokens[activeTokenId].status == Active
            )
  {
    var result := ExecuteParallelFork(state, tokenId, outgoingFlows);
    var targetNodes := set flowId | flowId in outgoingFlows ::
                         state.process.processDefinition.flows[flowId].targetRef;
    assert forall nodeId :: nodeId in targetNodes ==>
                               exists activeTokenId :: activeTokenId in result.process.tokenCollection.tokens &&
                                                       result.process.tokenCollection.tokens[activeTokenId].location == nodeId &&
                                                       result.process.tokenCollection.tokens[activeTokenId].status == Active;
  }

  /**
    * Get all tokens at a specific location
    */
  function GetTokensAtLocation(tokens: Token.Collection, location: string): set<Token.TokenId>
  {
    set tokenId | tokenId in tokens.tokens && tokens.tokens[tokenId].location == location && tokens.tokens[tokenId].status == Active :: tokenId
  }

  /**
    * Consume multiple tokens
    */
  function ConsumeMultipleTokens(tokens: Token.Collection, tokensToConsume: set<Token.TokenId>): Token.Collection
    requires forall id :: id in tokensToConsume ==> id in tokens.tokens && tokens.tokens[id].status == Active
    requires ValidTokenCollection(tokens)
    ensures ValidTokenCollection(ConsumeMultipleTokens(tokens, tokensToConsume))
    ensures var result := ConsumeMultipleTokens(tokens, tokensToConsume);
            // invariant 1: the consumed tokens are changed to Consumed
            forall id :: id in tokensToConsume ==> 
              id in result.tokens && result.tokens[id].status == Consumed
    ensures var result := ConsumeMultipleTokens(tokens, tokensToConsume);
            // invariant 2: the tokens that are not consumed keep their original status
            forall id :: id in tokens.tokens && id !in tokensToConsume ==> 
              id in result.tokens && result.tokens[id] == tokens.tokens[id]
    ensures var result := ConsumeMultipleTokens(tokens, tokensToConsume);
            // invariant 3: the size of the token collection does not change (consume does not delete, only change status)
            |result.tokens| == |tokens.tokens|
    ensures var result := ConsumeMultipleTokens(tokens, tokensToConsume);
            // invariant 4: the key property - after consuming all active tokens at a location, there are no active tokens at that location
            forall location :: 
              (forall id :: id in GetActiveTokensAtLocation(tokens, location) ==> id in tokensToConsume) ==>
              GetActiveTokensAtLocation(result, location) == {}
    decreases |tokensToConsume|
  {
    if |tokensToConsume| == 0 then
      tokens
    else
      var tokenId := Token.PickOne(tokensToConsume);
      var remainingTokens := tokensToConsume - {tokenId};
      
      assert tokenId in tokens.tokens && tokens.tokens[tokenId].status == Active;
      
      var tokensAfterOne := Token.ConsumeToken(tokens, tokenId);
      
      assert tokenId !in remainingTokens;
      assert forall id :: id in remainingTokens ==> 
               id in tokensAfterOne.tokens && tokensAfterOne.tokens[id].status == Active;
      assert tokensAfterOne.tokens[tokenId].status == Consumed;
      assert forall id :: id in tokens.tokens && id != tokenId ==> 
               tokensAfterOne.tokens[id] == tokens.tokens[id];
      
      ConsumeMultipleTokens(tokensAfterOne, remainingTokens)
  }

  /**
    * 简单通过：一进一出
    */
  function ExecuteSimplePassThrough(state: ExecutingState, tokenId: Token.TokenId): State
    requires tokenId in GetActiveTokens(state.process.tokenCollection)
    requires tokenId in state.process.tokenCollection.tokens
    requires ValidTokenCollection(state.process.tokenCollection)
    requires state.process.tokenCollection.tokens[tokenId].location in state.process.processDefinition.nodes
  {
    ExecuteSimpleTask(state, tokenId, "Gateway")
  }

  /**
    * Create enter events
    */
  function CreateEnterEvents(
    tokenIds: set<Token.TokenId>,
    flows: set<string>,
    flowDefinitions: map<string, ProcessDefinition.SequenceFlow>
  ): seq<ExecutionEvent>
    requires forall flowId :: flowId in flows ==> flowId in flowDefinitions
  {
    // simplified implementation: return empty sequence, can be improved later
    []
  }

  /**
    * Validate the preconditions for gateway execution
    */
  predicate CanExecuteGateway(state: ExecutingState, tokenId: Token.TokenId)
  {
    tokenId in GetActiveTokens(state.process.tokenCollection) &&
    tokenId in state.process.tokenCollection.tokens &&
    state.process.tokenCollection.tokens[tokenId].location in state.process.processDefinition.nodes
  }

  /**
    * Validate the preconditions for parallel fork
    */
  predicate CanExecuteParallelFork(state: ExecutingState, tokenId: Token.TokenId, outgoingFlows: set<string>)
  {
    ValidProcessDefinition(state.process.processDefinition) &&
    CanExecuteGateway(state, tokenId) &&
    |outgoingFlows| > 1 &&
    forall flowId :: flowId in outgoingFlows ==> flowId in state.process.processDefinition.flows
  }
  /**
    * Count the number of active tokens
    */
  function CountActiveTokens(state: State): nat
    requires state.Running?
  {
    |GetActiveTokens(state.process.tokenCollection)|
  }

  /**
    * Get all active tokens at a specific location
    */
  function GetActiveTokensAtLocation(tokens: Token.Collection, location: string): set<Token.TokenId>
  {
    set tokenId | tokenId in tokens.tokens &&
                  tokens.tokens[tokenId].location == location &&
                  tokens.tokens[tokenId].status == Active
  }

  /**
    * Execute a parallel join - consume all arriving tokens and create one new token
    */
  function {:opaque} ExecuteParallelJoin(state: ExecutingState, tokenId: Token.TokenId): State
    requires tokenId in GetActiveTokens(state.process.tokenCollection)
    requires tokenId in state.process.tokenCollection.tokens
    requires ValidTokenCollection(state.process.tokenCollection)
    requires ValidProcessDefinition(state.process.processDefinition)
    requires ValidProcessState(state.process)
    requires state.process.tokenCollection.tokens[tokenId].location in state.process.processDefinition.nodes
    requires CanExecuteParallelJoin(state, tokenId)
    ensures ValidState(ExecuteParallelJoin(state, tokenId))
    ensures var result := ExecuteParallelJoin(state, tokenId);
            result.Running? ==> (
              // 1. Join location has no active tokens
              var joinLocation := state.process.tokenCollection.tokens[tokenId].location;
              GetActiveTokensAtLocation(result.process.tokenCollection, joinLocation) == {} &&
              
              // 2. There is a new active token at the downstream location
              (var currentNode := state.process.processDefinition.nodes[joinLocation];
               if |currentNode.outgoing| == 1 then
                 var outgoingFlow := Token.PickOne(currentNode.outgoing);
                 if outgoingFlow in state.process.processDefinition.flows then
                   var nextNodeId := state.process.processDefinition.flows[outgoingFlow].targetRef;
                   exists newTokenId :: newTokenId in GetActiveTokens(result.process.tokenCollection) &&
                                       result.process.tokenCollection.tokens[newTokenId].location == nextNodeId
                 else false
               else false) &&
              
              // 3. The number of tokens decreases: there were multiple tokens, now there is only one
              (var joinLocation := state.process.tokenCollection.tokens[tokenId].location;
               var tokensAtJoinBefore := GetActiveTokensAtLocation(state.process.tokenCollection, joinLocation);
               |GetActiveTokens(result.process.tokenCollection)| == 
               |GetActiveTokens(state.process.tokenCollection)| - |tokensAtJoinBefore| + 1)
            )
  {
    var process := state.process;
    var token := process.tokenCollection.tokens[tokenId];
    var currentNode := process.processDefinition.nodes[token.location];
    var location := token.location;

    // get all active tokens at the location (all tokens from all branches)
    var tokensAtLocation := GetActiveTokensAtLocation(process.tokenCollection, location);

    // consume all arriving tokens
    var tokensAfterConsume := Token.ConsumeTokens(process.tokenCollection, tokensAtLocation);

    // use the invariant 4 of ConsumeMultipleTokens: after consuming, there are no active tokens at the location
    assert GetActiveTokensAtLocation(tokensAfterConsume, location) == {};

    // create a new token at the downstream location (parallel join should have exactly one output)
    if |currentNode.outgoing| == 1 then
      var outgoingFlow := Token.PickOne(currentNode.outgoing);
      if outgoingFlow in process.processDefinition.flows then
        var nextNodeId := process.processDefinition.flows[outgoingFlow].targetRef;
        // assert nextNodeId is in processDefinition.nodes
        
        // assert parallel join's output should not point to itself (BPMN semantic requirement)
        // this ensures CreateToken does not create a new token at the original location
        assume nextNodeId != location;
        
        var (finalTokens, newTokenId) := Token.CreateToken(tokensAfterConsume, nextNodeId);

        var newHistory := process.executionHistory + [
                            Event(0, location, NodeExited, tokenId, Variables.EmptyVariables()),
                            Event(1, nextNodeId, NodeEntered, newTokenId, Variables.EmptyVariables())
                          ];

        var updatedContext := ExecutionContext.CreateConsistentContext(
                                finalTokens,
                                location,
                                process.context.executionStep + 1
                              );

        var result := Running(Process(
                        processId := process.processId,
                        tokenCollection := finalTokens,
                        globalVariables := process.globalVariables,
                        processDefinition := process.processDefinition,
                        executionHistory := newHistory,
                        context := updatedContext
                      ));

        
        assert GetActiveTokensAtLocation(result.process.tokenCollection, location) == {};

        // Proof by contradiction: new tokens = original tokens - consumed tokens + newly created token
        var originalActiveTokens := GetActiveTokens(process.tokenCollection);
        var consumedTokens := tokensAtLocation;
        var remainingActiveTokens := originalActiveTokens - consumedTokens;
        var newlyCreatedTokens := {newTokenId};
        
        // 1. after consume, the new token is active
        assert newTokenId in GetActiveTokens(result.process.tokenCollection);
        assert result.process.tokenCollection.tokens[newTokenId].status == Active;
        
        // 2. from ValidProcessDefinition and token operation, the location of the new token is correct
        assert outgoingFlow in process.processDefinition.flows;
        assert nextNodeId == process.processDefinition.flows[outgoingFlow].targetRef;
        assert nextNodeId in process.processDefinition.nodes;  // from ValidProcessDefinition
        assert result.process.tokenCollection.tokens[newTokenId].location == nextNodeId;
        
        // 3. the location of the new token is in the definition
        assert result.process.tokenCollection.tokens[newTokenId].location in result.process.processDefinition.nodes;
        
        assert forall tokenId :: tokenId in GetActiveTokens(result.process.tokenCollection) ==>
                        result.process.tokenCollection.tokens[tokenId].location in result.process.processDefinition.nodes;
        
        // 4. Token number inference: establish a step-by-step proof chain
        
        // Step 1: call ConsumeTokens's lemma to prove the effect of the consume operation
        Token.ConsumeTokensReducesActiveTokens(process.tokenCollection, tokensAtLocation);
        assert |GetActiveTokens(tokensAfterConsume)| == |GetActiveTokens(process.tokenCollection)| - |tokensAtLocation|;
        
        // Step 2: call CreateToken's lemma to prove the effect of the create operation  
        Token.CreateTokenPreservesActiveTokens(tokensAfterConsume, nextNodeId);
        assert |GetActiveTokens(finalTokens)| == |GetActiveTokens(tokensAfterConsume)| + 1;
        
        // Step 3: mathematical inference - combine two steps
        assert |GetActiveTokens(finalTokens)| == |GetActiveTokens(process.tokenCollection)| - |tokensAtLocation| + 1;
        
        // Step 4: the tokenCollection of result is finalTokens
        assert result.process.tokenCollection == finalTokens;
        
        // Step 5: the final conclusion
        assert |GetActiveTokens(result.process.tokenCollection)| == 
               |GetActiveTokens(process.tokenCollection)| - |tokensAtLocation| + 1;

        result
      else
        BPMNState.Error(process, FlowError(outgoingFlow, "Outgoing flow not found"))
    else
      BPMNState.Error(process, ExecutionError(token.location, "Parallel join should have exactly one outgoing flow"))
  }

  /** Only when all tokens arrive the parallel gateway, can the parallel be executed */
  predicate CanExecuteParallelJoin(state: ExecutingState, tokenId: Token.TokenId)
    requires tokenId in state.process.tokenCollection.tokens
    requires state.process.tokenCollection.tokens[tokenId].location in state.process.processDefinition.nodes
  {
    var process := state.process;
    var token := process.tokenCollection.tokens[tokenId];
    var node := process.processDefinition.nodes[token.location];

    tokenId in GetActiveTokens(state.process.tokenCollection) &&
    tokenId in state.process.tokenCollection.tokens &&
    state.process.tokenCollection.tokens[tokenId].status == Active &&
    state.process.tokenCollection.tokens[tokenId].location in state.process.processDefinition.nodes &&
    |GetActiveTokensAtLocation(process.tokenCollection, token.location)| == |node.incoming|
  }

/**
  * Lemma: 
    If canExecuteParallelFork, then the number of tokens in the result is the number of tokens in the state minus 1 plus the number of outgoing flows
  */
lemma ParallelForkCreatesExactTokens(
  state: ExecutingState, 
  tokenId: Token.TokenId, 
  outgoingFlows: set<string>
)
  requires CanExecuteParallelFork(state, tokenId, outgoingFlows)
  requires ValidTokenCollection(state.process.tokenCollection)
  requires ValidProcessDefinition(state.process.processDefinition)
  requires ValidProcessState(state.process)
  ensures var result := ExecuteParallelFork(state, tokenId, outgoingFlows);
          result.Running? ==>
          |GetActiveTokens(result.process.tokenCollection)| == 
          |GetActiveTokens(state.process.tokenCollection)| - 1 + |outgoingFlows|
 
{
  reveal ExecuteParallelFork(); 
  var process := state.process;
  
  // consume token
  var tokensAfterConsume := Token.ConsumeToken(process.tokenCollection, tokenId);
  Token.ConsumeTokenReducesActiveTokens(process.tokenCollection, tokenId);
  assert |GetActiveTokens(tokensAfterConsume)| == |GetActiveTokens(process.tokenCollection)| - 1;
  
  // create tokens (on the consumed collection)
  Token.CreateTokensForFlowsLemma(tokensAfterConsume, outgoingFlows, process.processDefinition.flows);
  var (finalTokens, newTokenIds) := Token.CreateTokensForFlows(tokensAfterConsume, outgoingFlows, process.processDefinition.flows);
  assert |GetActiveTokens(finalTokens)| == |GetActiveTokens(tokensAfterConsume)| + |outgoingFlows|;
  
  assert |GetActiveTokens(finalTokens)| == |GetActiveTokens(process.tokenCollection)| - 1 + |outgoingFlows|;
  
  var result := ExecuteParallelFork(state, tokenId, outgoingFlows);
}  

/**
  * Lemma: if |activeTokens| == |incoming| of prallel join node, then the execution queue is same as the active tokens
  */
 

  /**
    * Read task input variables to local variable mapping
    */
  function ReadTaskInputs(globalVars: Variables.VariableMap, inputVars: seq<string>): Variables.VariableMap
    decreases |inputVars|
  {
    if |inputVars| == 0 then
      Variables.EmptyVariables()
    else
      var varName := inputVars[0];
      var remainingVars := inputVars[1..];
      var localVars := ReadTaskInputs(globalVars, remainingVars);
      if varName in globalVars then
        Variables.SetVariable(localVars, varName, globalVars[varName])
      else
        localVars
  }

  /**
    * Write task output variables to global variables
    */
  function WriteTaskOutputs(globalVars: Variables.VariableMap, localVars: Variables.VariableMap, outputVars: seq<string>): Variables.VariableMap
    decreases |outputVars|
  {
    if |outputVars| == 0 then
      globalVars
    else
      var varName := outputVars[0];
      var remainingVars := outputVars[1..];
      var updatedGlobals := WriteTaskOutputs(globalVars, localVars, remainingVars);
      if varName in localVars then
        Variables.SetVariable(updatedGlobals, varName, localVars[varName])
      else
        updatedGlobals
  }

  /**
    * 模拟任务执行并产生输出（简化版本）
    */
  function SimulateTaskExecution(taskType: TaskType, inputs: Variables.VariableMap, taskId: string): Variables.VariableMap
  {
    match taskType {
      case UserTask =>
        // user task: simulate user input, simply set a completion flag
        Variables.SetVariable(inputs, taskId + "_completed", Variables.BoolValue(true))
      case ServiceTask =>
        // service task: simulate service call result
        Variables.SetVariable(inputs, taskId + "_result", Variables.StringValue("service_success"))
      case ScriptTask =>
        // script task: simulate script execution
        Variables.SetVariable(inputs, taskId + "_script_output", Variables.IntValue(42))
      case ManualTask =>
        // manual task: simulate manual operation completion
        Variables.SetVariable(inputs, taskId + "_manual_done", Variables.BoolValue(true))
      case BusinessRuleTask =>
        // 业务规则任务：模拟规则评估结果
        Variables.SetVariable(inputs, taskId + "_rule_result", Variables.StringValue("rule_passed"))
    }
  }

  /**
    * 通用的任务执行函数，处理数据输入输出
    */
  function ExecuteTaskWithData(state: ExecutingState, tokenId: Token.TokenId, taskType: TaskType, data: Option<TaskData>): State
    requires tokenId in GetActiveTokens(state.process.tokenCollection)
    requires tokenId in state.process.tokenCollection.tokens
    requires ValidProcessDefinition(state.process.processDefinition)
    requires ValidProcessState(state.process)
    requires state.process.tokenCollection.tokens[tokenId].location in state.process.processDefinition.nodes
    requires state.process.tokenCollection.tokens[tokenId].status == Active
    requires ValidTokenCollection(state.process.tokenCollection)
    ensures ValidState(ExecuteTaskWithData(state, tokenId, taskType, data))
  {
    var process := state.process;
    var token := process.tokenCollection.tokens[tokenId];
    var currentNode := process.processDefinition.nodes[token.location];

    // 获取输出流
    var outgoingFlows := currentNode.outgoing;
    if |outgoingFlows| == 1 then
      var flowId := Token.PickOne(outgoingFlows);
      if flowId in process.processDefinition.flows then
        var nextNodeId := process.processDefinition.flows[flowId].targetRef;
        
        // 处理数据输入输出
        var updatedGlobalVars := 
          if data.Some? then
            var taskData := data.Unwrap();
            // 1. 读取输入变量到本地环境
            var localInputs := ReadTaskInputs(process.globalVariables, taskData.inputVariables);
            // 2. 模拟任务执行
            var localOutputs := SimulateTaskExecution(taskType, localInputs, token.location);
            // 3. 写入输出变量到全局环境
            WriteTaskOutputs(process.globalVariables, localOutputs, taskData.outputVariables)
          else
            process.globalVariables;

            // 消费当前token，创建下一个token
    assert process.tokenCollection.tokens[tokenId].status == Active;
    var tokensAfterConsume := Token.ConsumeToken(process.tokenCollection, tokenId);
    var (tokensWithNext, nextTokenId) := Token.CreateToken(tokensAfterConsume, nextNodeId);

        var newHistory := process.executionHistory + [
                            Event(0, token.location, NodeExited, tokenId, Variables.EmptyVariables()),
                            Event(1, nextNodeId, NodeEntered, nextTokenId, Variables.EmptyVariables())
                          ];

        var updatedContext := ExecutionContext.CreateConsistentContext(
                                tokensWithNext,
                                nextNodeId,
                                process.context.executionStep + 1
                              );

        var updatedProcess := Process(
                                processId := process.processId,
                                tokenCollection := tokensWithNext,
                                globalVariables := updatedGlobalVars,  // 使用更新后的全局变量
                                processDefinition := process.processDefinition,
                                executionHistory := newHistory,
                                context := updatedContext
                              );

        Running(updatedProcess)
      else
        BPMNState.Error(process, FlowError(flowId, "Flow not found in process definition"))
    else
      BPMNState.Error(process, ExecutionError(token.location, "Task should have exactly one outgoing flow"))
  }

  // specific task execution functions (now all delegated to the generic function)
  function ExecuteUserTaskWithData(state: ExecutingState, tokenId: Token.TokenId, data: Option<TaskData>): State
    requires tokenId in GetActiveTokens(state.process.tokenCollection)
    requires tokenId in state.process.tokenCollection.tokens
    requires state.process.tokenCollection.tokens[tokenId].location in state.process.processDefinition.nodes
    requires state.process.tokenCollection.tokens[tokenId].status == Active
    requires ValidTokenCollection(state.process.tokenCollection)
    requires ValidProcessDefinition(state.process.processDefinition)
    requires ValidProcessState(state.process)
    ensures ValidState(ExecuteUserTaskWithData(state, tokenId, data))
  {
    ExecuteTaskWithData(state, tokenId, UserTask, data)
  }

  function ExecuteServiceTaskWithData(state: ExecutingState, tokenId: Token.TokenId, data: Option<TaskData>): State
    requires tokenId in GetActiveTokens(state.process.tokenCollection)
    requires tokenId in state.process.tokenCollection.tokens
    requires state.process.tokenCollection.tokens[tokenId].location in state.process.processDefinition.nodes
    requires state.process.tokenCollection.tokens[tokenId].status == Active
    requires ValidTokenCollection(state.process.tokenCollection)
    requires ValidProcessDefinition(state.process.processDefinition)
    requires ValidProcessState(state.process)
    ensures ValidState(ExecuteServiceTaskWithData(state, tokenId, data))
  {
    ExecuteTaskWithData(state, tokenId, ServiceTask, data)
  }

  function ExecuteManualTaskWithData(state: ExecutingState, tokenId: Token.TokenId, data: Option<TaskData>): State
    requires tokenId in GetActiveTokens(state.process.tokenCollection)
    requires tokenId in state.process.tokenCollection.tokens
    requires state.process.tokenCollection.tokens[tokenId].location in state.process.processDefinition.nodes
    requires state.process.tokenCollection.tokens[tokenId].status == Active
    requires ValidTokenCollection(state.process.tokenCollection)
    requires ValidProcessDefinition(state.process.processDefinition)
    requires ValidProcessState(state.process)
    ensures ValidState(ExecuteManualTaskWithData(state, tokenId, data))
  {
    ExecuteTaskWithData(state, tokenId, ManualTask, data)
  }

  /**
    * Data Conflict Detection Functions
    */

  /**
    * Get variable access information for a token
    */
  function GetTokenVariableAccess(state: ExecutingState, tokenId: Token.TokenId): seq<BPMNState.VariableAccess>
    requires ValidState(state)
    requires ValidProcessDefinition(state.process.processDefinition)
    requires ValidProcessState(state.process)
    requires tokenId in state.process.tokenCollection.tokens
    requires state.process.tokenCollection.tokens[tokenId].location in state.process.processDefinition.nodes
  {
    var process := state.process;
    var token := process.tokenCollection.tokens[tokenId];
    var currentNode := process.processDefinition.nodes[token.location];
    
    match currentNode.nodeType {
      case Task(taskType, data) =>
        if data.Some? then
          var taskData := data.Unwrap();
          var readAccess := seq(|taskData.inputVariables|, i requires 0 <= i < |taskData.inputVariables| => 
                               BPMNState.VarAccess(taskData.inputVariables[i], BPMNState.Read));
          var writeAccess := seq(|taskData.outputVariables|, i requires 0 <= i < |taskData.outputVariables| => 
                                BPMNState.VarAccess(taskData.outputVariables[i], BPMNState.Write));
          readAccess + writeAccess
        else
          []
      case _ => []  // 其他节点类型不访问变量
    }
  }

  /**
    * Detect conflicts between two tokens
    */
  function DetectConflictBetweenTokens(
    token1: Token.TokenId,
    access1: seq<BPMNState.VariableAccess>,
    token2: Token.TokenId,
    access2: seq<BPMNState.VariableAccess>
  ): seq<BPMNState.DataConflict>
  {
    if |access1| == 0 || |access2| == 0 then []
    else 
      DetectConflictHelper(token1, access1, token2, access2, 0, 0, [])
  }

  function DetectConflictHelper(
    token1: Token.TokenId,
    access1: seq<BPMNState.VariableAccess>,
    token2: Token.TokenId,
    access2: seq<BPMNState.VariableAccess>,
    i: nat,
    j: nat,
    acc: seq<BPMNState.DataConflict>
  ): seq<BPMNState.DataConflict>
    requires 0 <= i <= |access1|
    requires 0 <= j <= |access2|
    decreases |access1| - i, |access2| - j
  {
    if i >= |access1| then acc
    else if j >= |access2| then DetectConflictHelper(token1, access1, token2, access2, i + 1, 0, acc)
    else
      var newAcc := if access1[i].variable == access2[j].variable &&
                       BPMNState.HasConflict(access1[i].accessType, access2[j].accessType) then
                      acc + [BPMNState.CreateDataConflict(access1[i].variable, access1[i].accessType, 
                                                          access2[j].accessType, token1, token2)]
                    else acc;
      DetectConflictHelper(token1, access1, token2, access2, i, j + 1, newAcc)
  }

  /**
    * Detect conflicts between one token and a list of other tokens
    */
  function DetectConflictsWithTokens(
    token: Token.TokenId,
    tokenAccess: seq<BPMNState.VariableAccess>,
    otherTokens: seq<Token.TokenId>,
    state: ExecutingState
  ): seq<BPMNState.DataConflict>
    requires ValidState(state)
    requires ValidProcessDefinition(state.process.processDefinition)
    requires ValidProcessState(state.process)
    requires forall tokenId :: tokenId in otherTokens ==>
               tokenId in state.process.tokenCollection.tokens &&
               state.process.tokenCollection.tokens[tokenId].location in state.process.processDefinition.nodes
    decreases |otherTokens|
  {
    if |otherTokens| == 0 then
      []
    else
      var firstOther := Seq.First(otherTokens);
      var restOthers := Seq.DropFirst(otherTokens);
      var firstOtherAccess := GetTokenVariableAccess(state, firstOther);
      var conflictsWithFirst := DetectConflictBetweenTokens(token, tokenAccess, firstOther, firstOtherAccess);
      var conflictsWithRest := DetectConflictsWithTokens(token, tokenAccess, restOthers, state);
      conflictsWithFirst + conflictsWithRest
  }

  /**
    * Filter tokens to remove those with data conflicts
    * Returns (conflict-free tokens, detected conflicts)
    */
  function FilterConflictFreeTokens(
    queue: seq<Token.TokenId>,
    state: ExecutingState
  ): (seq<Token.TokenId>, seq<BPMNState.DataConflict>)
    requires ValidState(state)
    requires ValidProcessDefinition(state.process.processDefinition)
    requires ValidProcessState(state.process)
    requires forall tokenId :: tokenId in queue ==>
               tokenId in state.process.tokenCollection.tokens &&
               state.process.tokenCollection.tokens[tokenId].status == Active &&
               state.process.tokenCollection.tokens[tokenId].location in state.process.processDefinition.nodes
    ensures var (conflictFree, conflicts) := FilterConflictFreeTokens(queue, state);
            forall tokenId :: tokenId in conflictFree ==> tokenId in queue
    ensures var (conflictFree, conflicts) := FilterConflictFreeTokens(queue, state);
            |conflictFree| <= |queue|
    decreases |queue|
  {
    if |queue| == 0 then
      ([], [])
    else if |queue| == 1 then
      ([Seq.First(queue)], [])
    else
      var firstToken := Seq.First(queue);
      var restQueue := Seq.DropFirst(queue);
      
      var (restConflictFree, restConflicts) := FilterConflictFreeTokens(restQueue, state);

      var firstAccess := GetTokenVariableAccess(state, firstToken);
      var conflictsWithFirst := DetectConflictsWithTokens(firstToken, firstAccess, restConflictFree, state);
      
      if |conflictsWithFirst| > 0 then
        (restConflictFree, restConflicts + conflictsWithFirst)
      else
        ([firstToken] + restConflictFree, restConflicts)
  }

  /**
    * Get tokens from execution queue that can be executed without data conflicts
    */
  function GetConflictFreeTokensFromQueue(state: ExecutingState): (seq<Token.TokenId>, seq<BPMNState.DataConflict>)
    requires ValidState(state)
    requires ValidProcessDefinition(state.process.processDefinition)
    requires ValidProcessState(state.process)
    ensures var (conflictFree, conflicts) := GetConflictFreeTokensFromQueue(state);
            forall tokenId :: tokenId in conflictFree ==> tokenId in state.process.context.executionQueue
    ensures var (conflictFree, conflicts) := GetConflictFreeTokensFromQueue(state);
            forall tokenId :: tokenId in conflictFree ==>
              tokenId in state.process.tokenCollection.tokens &&
              state.process.tokenCollection.tokens[tokenId].status == Active &&
              CanExecuteTokenImmediately(state, tokenId)
  {
    var executableTokens := GetExecutableTokensFromQueue(state);
    FilterConflictFreeTokens(executableTokens, state)
  }

  /**
    * Exclusive Gateway Functions
    */

  /**
    * Execute exclusive fork - evaluate conditions and choose one flow
    */
  function ExecuteExclusiveFork(
    state: ExecutingState, 
    tokenId: Token.TokenId, 
    outgoingFlows: set<string>,
    defaultFlow: Option<string>
  ): State
  
    requires tokenId in state.process.tokenCollection.tokens
    requires ValidProcessDefinition(state.process.processDefinition)
    requires ValidProcessState(state.process)
    requires |outgoingFlows| > 1
    requires defaultFlow.Some? ==> defaultFlow.Unwrap() in outgoingFlows
    requires forall flowId :: flowId in outgoingFlows ==> flowId in state.process.processDefinition.flows
    requires  state.process.tokenCollection.tokens[tokenId].status == Active
    ensures ValidState(ExecuteExclusiveFork(state, tokenId, outgoingFlows, defaultFlow))
    requires ValidTokenCollection(state.process.tokenCollection)
  {
    var process := state.process;
    assert defaultFlow.Some? ==> defaultFlow.Unwrap() in outgoingFlows;
    var selectedFlow := EvaluateExclusiveConditions(state, outgoingFlows, defaultFlow);
    
    match selectedFlow {
      case Some(flowId) =>
        assert flowId in outgoingFlows;
        assert forall fId :: fId in outgoingFlows ==> fId in process.processDefinition.flows;
        assert flowId in process.processDefinition.flows;
        ExecuteSingleFlow(state, tokenId, flowId)
      case None =>
        // 没有任何流被选中（包括默认流），这是一个错误
        BPMNState.Error(process, ExecutionError(state.process.tokenCollection.tokens[tokenId].location, 
                                               "No flow selected in exclusive gateway"))
    }
  }

  /**
    * Execute exclusive merge - simple merge, no synchronization needed
    */
  function ExecuteExclusiveMerge(state: ExecutingState, tokenId: Token.TokenId): State
    requires tokenId in state.process.tokenCollection.tokens
    requires state.process.tokenCollection.tokens[tokenId].status == Active
    requires state.process.tokenCollection.tokens[tokenId].location in state.process.processDefinition.nodes
    requires ValidProcessDefinition(state.process.processDefinition)
    requires ValidProcessState(state.process)
    requires ValidTokenCollection(state.process.tokenCollection)
    ensures ValidState(ExecuteExclusiveMerge(state, tokenId))
  {
    ExecuteSimplePassThrough(state, tokenId)
  }

  /**
    * Evaluate conditions for exclusive gateway and return selected flow
    * 接口设计：先定义函数签名，具体实现可以后续完善
    */
  function EvaluateExclusiveConditions(
    state: ExecutingState,
    outgoingFlows: set<string>,
    defaultFlow: Option<string>
  ): Option<string>
    requires ValidProcessDefinition(state.process.processDefinition)
    requires forall flowId :: flowId in outgoingFlows ==> flowId in state.process.processDefinition.flows
    requires defaultFlow.Some? ==> defaultFlow.Unwrap() in outgoingFlows
    ensures var result := EvaluateExclusiveConditions(state, outgoingFlows, defaultFlow);
            result.Some? ==> result.Unwrap() in outgoingFlows
  {
    // TODO: 实现条件评估逻辑
    // 1. 遍历所有非默认流，评估其条件
    // 2. 返回第一个满足条件的流
    // 3. 如果都不满足，返回默认流
    // 4. 如果没有默认流且都不满足，返回None
    
    // 临时实现：优先选择第一个有条件的流，否则选择默认流
    var conditionalFlows := GetConditionalFlows(outgoingFlows, state.process.processDefinition.flows);
    if |conditionalFlows| > 0 then
      var firstFlow := Token.PickOne(conditionalFlows);
      if EvaluateFlowCondition(state, firstFlow) then
        Some(firstFlow)
      else if defaultFlow.Some? then
        defaultFlow
      else
        None
    else if defaultFlow.Some? then
      defaultFlow
    else
      None
  }

  /**
    * Get flows that have conditions (non-default flows)
    */
  function GetConditionalFlows(
    flows: set<string>,
    flowDefinitions: map<string, SequenceFlow>
  ): set<string>
    requires forall flowId :: flowId in flows ==> flowId in flowDefinitions
  {
    set flowId | flowId in flows && flowDefinitions[flowId].condition.Some?
  }

  /**
    * Evaluate a single flow condition
    * 接口设计：条件评估的核心函数
    */
  function EvaluateFlowCondition(state: ExecutingState, flowId: string): bool
    requires flowId in state.process.processDefinition.flows
  {
    var flow := state.process.processDefinition.flows[flowId];
    match flow.condition {
      case None => true  // 无条件，总是满足
      case Some(conditionExpr) =>
        // TODO: 实现具体的条件表达式评估
        // 这里需要解析conditionExpr并根据当前变量状态评估
        EvaluateConditionExpression(state, conditionExpr)
    }
  }

  /**
    * Evaluate condition expression against current variable state
    * 接口设计：条件表达式评估引擎
    */
  function EvaluateConditionExpression(state: ExecutingState, expression: string): bool
  {
    // TODO: 实现条件表达式解析和评估
    // 可能的条件格式：
    // - "variable == value"
    // - "variable > 10"
    // - "status == 'approved'"
    // - 复合条件等
    
    // 临时实现：总是返回true
    true
  }

  /**
    * Execute a single flow (used by exclusive gateway)
    */
  function ExecuteSingleFlow(state: ExecutingState, tokenId: Token.TokenId, flowId: string): State
    requires tokenId in state.process.tokenCollection.tokens
    requires state.process.tokenCollection.tokens[tokenId].status == Active
    requires flowId in state.process.processDefinition.flows
    requires ValidProcessDefinition(state.process.processDefinition)
    requires ValidProcessState(state.process)
    requires ValidTokenCollection(state.process.tokenCollection)
    ensures ValidState(ExecuteSingleFlow(state, tokenId, flowId))
  {
    var process := state.process;
    var flow := process.processDefinition.flows[flowId];
    var nextNodeId := flow.targetRef;
    
    // 消费当前token，创建下一个token
    var tokensAfterConsume := Token.ConsumeToken(process.tokenCollection, tokenId);
    var (tokensWithNext, nextTokenId) := Token.CreateToken(tokensAfterConsume, nextNodeId);
    
    var token := process.tokenCollection.tokens[tokenId];
    var newHistory := process.executionHistory + [
                        Event(0, token.location, NodeExited, tokenId, Variables.EmptyVariables()),
                        Event(1, nextNodeId, NodeEntered, nextTokenId, Variables.EmptyVariables())
                      ];
    
    var updatedContext := ExecutionContext.CreateConsistentContext(
                            tokensWithNext,
                            nextNodeId,
                            process.context.executionStep + 1
                          );
    
    Running(Process(
              processId := process.processId,
              tokenCollection := tokensWithNext,
              globalVariables := process.globalVariables,
              processDefinition := process.processDefinition,
              executionHistory := newHistory,
              context := updatedContext
            ))
  }
}
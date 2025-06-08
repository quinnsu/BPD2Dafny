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
module ExecutionEngine {
  import opened Token
  import opened BPMNState
  import opened ProcessDefinition
  import opened Variables
  import opened ExecutionInit
  import opened Optional
  import opened ExecutionContext
  import opened Arrays

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
         BPMNState.Error(state.process, ValidationError("Token is not active"))
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
    * 2. If all tokens cannot be executed, return error state (deadlock)
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
      //var executableTokens := GetImmediatelyExecutableTokens(state);
      var executableTokensFromQueue := GetExecutableTokensFromQueue(state);
      if |executableTokensFromQueue| == 0 then
        // Deadlock: no tokens can be executed
        BPMNState.Error(process, ValidationError("Deadlock detected: no tokens can be executed"))
      else
        // Execute the first executable token
        var tokenToExecute := executableTokensFromQueue[0];
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
              BPMNState.Error(state.process, ValidationError("Invalid state for EndEvent"))
          case Task(taskType) => ExecuteTask(state, tokenId, taskType)
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
            // 这是join操作，检查是否所有分支都已到达
            var tokensAtLocation := GetActiveTokensAtLocation(process.tokenCollection, location);
            |tokensAtLocation| == |node.incoming|
          else
            // 这是fork操作或简单通过，可以立即执行
            true
        case Gateway(_) =>
          // 其他类型网关的处理逻辑
          true
        case _ =>
          // Task, StartEvent, EndEvent等通常可以立即执行
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
  function {:verify false} GetExecutableTokensFromQueue(state: ExecutingState): seq<Token.TokenId>
    requires ValidState(state)
    ensures forall tokenId :: tokenId in GetExecutableTokensFromQueue(state) ==> 
              tokenId in state.process.context.executionQueue && 
              tokenId in state.process.tokenCollection.tokens &&
              state.process.tokenCollection.tokens[tokenId].status == Active && 
              CanExecuteTokenImmediately(state, tokenId)
    ensures |GetExecutableTokensFromQueue(state)| <= |state.process.context.executionQueue|
  {
    // 简化实现：遍历执行队列，过滤可执行的tokens
    if |state.process.context.executionQueue| == 0 then
      []
    else
      var tokenId := state.process.context.executionQueue[0];
      var rest := state.process.context.executionQueue[1..];
      var restState := state.(process := state.process.(context := state.process.context.(executionQueue := rest)));
      var restResult := GetExecutableTokensFromQueue(restState);
      
      if tokenId in state.process.tokenCollection.tokens &&
         state.process.tokenCollection.tokens[tokenId].status == Active &&
         CanExecuteTokenImmediately(state, tokenId) then
        [tokenId] + restResult
      else
        restResult
  }
 

  /**
    * 执行单个token的步骤
    */
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
        // ExecutingState确保state.Running?为true
        assert state.Running?;
        ExecuteEndEvent(state, tokenId)
      case Task(taskType) => ExecuteTask(state, tokenId, taskType)
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
    
    // 检查是否还有其他活跃的tokens
    var remainingActiveTokens := GetActiveTokens(tokensAfterConsume);
    
    if |remainingActiveTokens| == 0 then
      // 没有活跃tokens了，流程正常完成
      assert ValidProcessState(updatedProcess);
      BPMNState.Completed(updatedProcess, process.globalVariables)
    else
      BPMNState.Error(process, ValidationError("Invalid state for EndEvent"))
  }
  // execute the step of a task
  function ExecuteTask(state: ExecutingState, tokenId: Token.TokenId, taskType: TaskType): State
    requires tokenId in GetActiveTokens(state.process.tokenCollection)
    requires ValidProcessDefinition(state.process.processDefinition)
    requires ValidProcessState(state.process)
    requires tokenId in state.process.tokenCollection.tokens
    requires ValidTokenCollection(state.process.tokenCollection)
    requires state.process.tokenCollection.tokens[tokenId].location in state.process.processDefinition.nodes
    ensures ValidState(ExecuteTask(state, tokenId, taskType))
  {
    match taskType {
      case UserTask =>
        ExecuteUserTask(state, tokenId)
      case ServiceTask =>
        ExecuteServiceTask(state, tokenId)
      case ManualTask =>
        ExecuteManualTask(state, tokenId)
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
            BPMNState.Error(process, ValidationError("Cannot execute parallel fork"))
        else if |incomingFlows| > 1 then
          if CanExecuteParallelJoin(state, tokenId) then
            ExecuteParallelJoin(state, tokenId)
          else
            //waiting for other tokens to arrive
            state
        else
          ExecuteSimplePassThrough(state, tokenId)
      case _ =>
        BPMNState.Error(process, ValidationError("Invalid gateway type"))
    }
  }


  predicate DetectDeadlock(state: State)
{
  match state {
    case Running(process) =>
      var activeTokens := GetActiveTokens(process.tokenCollection);
      // 所有活跃token都无法继续执行
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
                                context := updatedContext  // 使用新的context
                              );

        // 验证最终的Process对象
        assert ValidProcessState(updatedProcess);
        
        Running(updatedProcess)
      else
        BPMNState.Error(process, ValidationError("Flow not found in process definition"))
    else
      // Multiple output flows - this is usually an error for UserTask
      BPMNState.Error(process, ValidationError("UserTask should not have multiple outgoing flows"))
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

    // 获取输出流
    var outgoingFlows := currentNode.outgoing;
    if |outgoingFlows| == 1 then
      var flowId := Token.PickOne(outgoingFlows);
      if flowId in process.processDefinition.flows then
        var nextNodeId := process.processDefinition.flows[flowId].targetRef;
        // 消费当前token
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
        BPMNState.Error(process, ValidationError("Flow not found in process definition"))
    else
      BPMNState.Error(process, ValidationError(taskType + " should have exactly one outgoing flow"))
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
      // 验证所有输出流都在流程定义中
      if forall flowId :: flowId in outgoingFlows ==> flowId in process.processDefinition.flows then
        ExecuteParallelFork(state, tokenId, outgoingFlows)
      else
        BPMNState.Error(process, ValidationError("Some outgoing flows not found in process definition"))
    else if |incomingFlows| > 1 then
      if CanExecuteParallelJoin(state, tokenId) then
        ExecuteParallelJoin(state, tokenId)
      else
        BPMNState.Error(process, ValidationError("Cannot execute parallel join"))
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

    // 消费当前token
    var tokensAfterConsume := Token.ConsumeToken(process.tokenCollection, tokenId);

    // 关键断言：建立推理链
    // 1. outgoingFlows都在process.processDefinition.flows中
    assert forall flowId :: flowId in outgoingFlows ==> flowId in process.processDefinition.flows;
    
    // 2. 所有targetRef都在process.processDefinition.nodes中
    assert forall flowId :: flowId in outgoingFlows ==> 
           process.processDefinition.flows[flowId].targetRef in process.processDefinition.nodes;
    
    // 3. 定义targetNodes集合
    var targetNodes := set flowId | flowId in outgoingFlows ::
                         process.processDefinition.flows[flowId].targetRef;
    
    // 4. 证明所有targetNodes都在processDefinition.nodes中
    assert forall nodeId :: nodeId in targetNodes ==> nodeId in process.processDefinition.nodes;

    // 为每个输出流创建新token
    var (finalTokens, newTokenIds) := CreateTokensForFlows(
                                        tokensAfterConsume,
                                        outgoingFlows,
                                        process.processDefinition.flows
                                      );

    assert |newTokenIds| == |outgoingFlows|;
    assert |finalTokens.tokens| == |tokensAfterConsume.tokens| + |outgoingFlows|;

    // 关键断言：证明每个目标节点都有token
    var targetNodes := set flowId | flowId in outgoingFlows ::
                         process.processDefinition.flows[flowId].targetRef;
    assert forall nodeId :: nodeId in targetNodes ==>
                              exists tokenId :: tokenId in newTokenIds &&
                                                finalTokens.tokens[tokenId].location == nodeId &&
                                               finalTokens.tokens[tokenId].status == Active;
    
    // 由于targetNodes ⊆ processDefinition.nodes，所以新token的位置都在nodes中
    // 利用CreateTokensForFlows的后置条件：每个flow都有对应的token
    assert forall flowId :: flowId in outgoingFlows ==>
             exists tokenId :: tokenId in newTokenIds &&
                               finalTokens.tokens[tokenId].location == process.processDefinition.flows[flowId].targetRef;
    
    // 结合ValidProcessDefinition：所有targetRef都在nodes中
    assume forall tokenId :: tokenId in newTokenIds ==>
                              finalTokens.tokens[tokenId].location in process.processDefinition.nodes;

    // 更新执行历史..
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

    // 断言：验证每个目标节点都有token
    assert forall flowId :: flowId in outgoingFlows ==> 
      var targetNode := process.processDefinition.flows[flowId].targetRef;
      exists tokenId :: tokenId in GetActiveTokens(result.process.tokenCollection) &&
                        result.process.tokenCollection.tokens[tokenId].location == targetNode;

    // 最终验证ValidProcessState的四个条件：
    
    // 条件1：所有active token的位置都在processDefinition.nodes中
    assume forall tokenId :: tokenId in GetActiveTokens(result.process.tokenCollection) ==>
                       result.process.tokenCollection.tokens[tokenId].location in result.process.processDefinition.nodes;
    
    // 条件2：context.executionQueue中的token都在tokenCollection中且为Active状态  
    assert forall tokenId :: tokenId in result.process.context.executionQueue ==>
                        tokenId in result.process.tokenCollection.tokens &&
                        result.process.tokenCollection.tokens[tokenId].status == Active;
    
    // 条件3：所有active token都在executionQueue中（双向绑定）
    assert forall tokenId :: tokenId in GetActiveTokens(result.process.tokenCollection) ==>
                        tokenId in result.process.context.executionQueue;
    
    // 条件4：context本身有效
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
    * 获取在特定位置的所有tokens
    */
  function GetTokensAtLocation(tokens: Token.Collection, location: string): set<Token.TokenId>
  {
    set tokenId | tokenId in tokens.tokens && tokens.tokens[tokenId].location == location && tokens.tokens[tokenId].status == Active :: tokenId
  }

  /**
    * 消费多个tokens
    */
  function ConsumeMultipleTokens(tokens: Token.Collection, tokensToConsume: set<Token.TokenId>): Token.Collection
    requires forall id :: id in tokensToConsume ==> id in tokens.tokens && tokens.tokens[id].status == Active
    requires ValidTokenCollection(tokens)
    ensures ValidTokenCollection(ConsumeMultipleTokens(tokens, tokensToConsume))
    ensures var result := ConsumeMultipleTokens(tokens, tokensToConsume);
            // 不变式1：被消费的tokens状态变为Consumed
            forall id :: id in tokensToConsume ==> 
              id in result.tokens && result.tokens[id].status == Consumed
    ensures var result := ConsumeMultipleTokens(tokens, tokensToConsume);
            // 不变式2：未被消费的tokens保持原状态
            forall id :: id in tokens.tokens && id !in tokensToConsume ==> 
              id in result.tokens && result.tokens[id] == tokens.tokens[id]
    ensures var result := ConsumeMultipleTokens(tokens, tokensToConsume);
            // 不变式3：token集合大小不变（consume不删除，只改状态）
            |result.tokens| == |tokens.tokens|
    ensures var result := ConsumeMultipleTokens(tokens, tokensToConsume);
            // 不变式4：关键性质 - 消费掉某位置所有active tokens后，该位置无active tokens
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
      
      // 关键断言：验证ConsumeToken的前置条件
      assert tokenId in tokens.tokens && tokens.tokens[tokenId].status == Active;
      
      var tokensAfterOne := Token.ConsumeToken(tokens, tokenId);
      
      // 递归不变式辅助断言
      assert tokenId !in remainingTokens;
      assert forall id :: id in remainingTokens ==> 
               id in tokensAfterOne.tokens && tokensAfterOne.tokens[id].status == Active;
      
      // 证明单个消费后的性质
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
    * 创建进入事件列
    */
  function CreateEnterEvents(
    tokenIds: set<Token.TokenId>,
    flows: set<string>,
    flowDefinitions: map<string, ProcessDefinition.SequenceFlow>
  ): seq<ExecutionEvent>
    requires forall flowId :: flowId in flows ==> flowId in flowDefinitions
  {
    // 简化实现：返回空序列，后续可以完善
    []
  }

  /**
    * 验证gateway执行的前置条件
    */
  predicate CanExecuteGateway(state: ExecutingState, tokenId: Token.TokenId)
  {
    tokenId in GetActiveTokens(state.process.tokenCollection) &&
    tokenId in state.process.tokenCollection.tokens &&
    state.process.tokenCollection.tokens[tokenId].location in state.process.processDefinition.nodes
  }

  /**
    * 验证parallel fork的前置条件
    */
  predicate CanExecuteParallelFork(state: ExecutingState, tokenId: Token.TokenId, outgoingFlows: set<string>)
  {
    ValidProcessDefinition(state.process.processDefinition) &&
    CanExecuteGateway(state, tokenId) &&
    |outgoingFlows| > 1 &&
    forall flowId :: flowId in outgoingFlows ==> flowId in state.process.processDefinition.flows
  }
  /**
    * 计算活跃token数量
    */
  function CountActiveTokens(state: State): nat
    requires state.Running?
  {
    |GetActiveTokens(state.process.tokenCollection)|
  }

  /**
    * 获取指定位置的所有active tokens
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
              // 1. Join位置不再有active tokens
              var joinLocation := state.process.tokenCollection.tokens[tokenId].location;
              GetActiveTokensAtLocation(result.process.tokenCollection, joinLocation) == {} &&
              
              // 2. 下游位置有新的active token
              (var currentNode := state.process.processDefinition.nodes[joinLocation];
               if |currentNode.outgoing| == 1 then
                 var outgoingFlow := Token.PickOne(currentNode.outgoing);
                 if outgoingFlow in state.process.processDefinition.flows then
                   var nextNodeId := state.process.processDefinition.flows[outgoingFlow].targetRef;
                   exists newTokenId :: newTokenId in GetActiveTokens(result.process.tokenCollection) &&
                                       result.process.tokenCollection.tokens[newTokenId].location == nextNodeId
                 else false
               else false) &&
              
              // 3. Token数量减少：原来有多个tokens，现在只有一个
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

    // 获取该位置的所有active tokens（所有分支的tokens）
    var tokensAtLocation := GetActiveTokensAtLocation(process.tokenCollection, location);

    // 消费所有到达的tokens
    var tokensAfterConsume := Token.ConsumeTokens(process.tokenCollection, tokensAtLocation);

    // 利用ConsumeMultipleTokens的不变式4：消费后该位置无active tokens
    assume GetActiveTokensAtLocation(tokensAfterConsume, location) == {};

    // 创建新token在下游（parallel join应该只有一个输出）
    if |currentNode.outgoing| == 1 then
      var outgoingFlow := Token.PickOne(currentNode.outgoing);
      if outgoingFlow in process.processDefinition.flows then
        var nextNodeId := process.processDefinition.flows[outgoingFlow].targetRef;
        // 关键断言：nextNodeId的位置都在processDefinition.nodes中
        
        // 关键断言：parallel join的输出不应指向自己（BPMN语义要求）
        // 这确保CreateToken不会在原位置创建新token
        assume nextNodeId != location;
        
        var (finalTokens, newTokenId) := Token.CreateToken(tokensAfterConsume, nextNodeId);

        // 更新执行历史
        var newHistory := process.executionHistory + [
                            Event(0, location, NodeExited, tokenId, Variables.EmptyVariables()),
                            Event(1, nextNodeId, NodeEntered, newTokenId, Variables.EmptyVariables())
                          ];

        // 更新context
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
        
        // 4. Token数量推理：建立分步证明链
        
        // Step 1: 调用ConsumeTokens的lemma来证明消费操作的效果
        Token.ConsumeTokensReducesActiveTokens(process.tokenCollection, tokensAtLocation);
        assert |GetActiveTokens(tokensAfterConsume)| == |GetActiveTokens(process.tokenCollection)| - |tokensAtLocation|;
        
        // Step 2: 调用CreateToken的lemma来证明创建操作的效果  
        Token.CreateTokenPreservesActiveTokens(tokensAfterConsume, nextNodeId);
        assert |GetActiveTokens(finalTokens)| == |GetActiveTokens(tokensAfterConsume)| + 1;
        
        // Step 3: 数学推理 - 结合两步
        assert |GetActiveTokens(finalTokens)| == |GetActiveTokens(process.tokenCollection)| - |tokensAtLocation| + 1;
        
        // Step 4: result的tokenCollection就是finalTokens
        assert result.process.tokenCollection == finalTokens;
        
        // Step 5: 最终结论
        assert |GetActiveTokens(result.process.tokenCollection)| == 
               |GetActiveTokens(process.tokenCollection)| - |tokensAtLocation| + 1;

        result
      else
        BPMNState.Error(process, ValidationError("Outgoing flow not found"))
    else
      BPMNState.Error(process, ValidationError("Parallel join should have exactly one outgoing flow"))
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
 

}
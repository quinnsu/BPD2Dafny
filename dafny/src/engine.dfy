/** 
  * Core Execution Engine
  */

include "./token.dfy"
include "./state.dfy"
include "./process.dfy"
include "./utils/variables.dfy"
include "./execution_init.dfy"
module ExecutionEngine {
  import opened Token
  import opened BPMNState
  import opened ProcessDefinition
  import opened Variables
  import opened ExecutionInit

  /**
    * The main execution function
    */
  function ExecuteStep(state: ExecutingState): State
    requires ValidState(state)
  {
    var process := state.process;
    var activeTokens := GetActiveTokens(process.tokenCollection);
    var tokenId := Token.PickOne(activeTokens);
    var token := process.tokenCollection.tokens[tokenId];
    var currentNode := process.processDefinition.nodes[token.location];

    match currentNode.nodeType {
      case StartEvent =>
        if CanExecuteStartEvent(state) then
          ExecuteStartEvent(state)
        else
          state
      case EndEvent => ExecuteEndEvent(state, tokenId)
      case Task(taskType) => ExecuteTask(state, tokenId, taskType)
      case Gateway(gatewayType) => ExecuteGateway(state, tokenId, gatewayType)
      case IntermediateEvent(eventType) => ExecuteIntermediateEvent(state, tokenId, eventType)
    }
  }


  // execute the step of a start event
  function {:verify false} ExecuteStartEvent(state: State): State
    requires CanExecuteStartEvent(state)
    ensures ExecuteStartEvent(state).Running?
  {
    ExecutionInit.ProcessStartEvent(state)
  }
  // execute the step of a end event
  function ExecuteEndEvent(state: State, tokenId: Token.TokenId): State { state }
  // execute the step of a task
  function ExecuteTask(state: ExecutingState, tokenId: Token.TokenId, taskType: TaskType): State
    requires tokenId in GetActiveTokens(state.process.tokenCollection)
    requires tokenId in state.process.tokenCollection.tokens
    requires state.process.tokenCollection.tokens[tokenId].location in state.process.processDefinition.nodes
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
  {
    var process := state.process;
    var token := process.tokenCollection.tokens[tokenId];
    var currentNode := process.processDefinition.nodes[token.location];
    var outgoingFlows := currentNode.outgoing;
    var incomingFlows := currentNode.incoming;

    if |outgoingFlows| > 1 then
      if CanExecuteParallelFork(state, tokenId, outgoingFlows) then
        ExecuteParallelFork(state, tokenId, outgoingFlows)
      else
        BPMNState.Error(process, ValidationError("Cannot execute parallel fork"))
    else if |incomingFlows| > 1 then
      state
    else
      ExecuteSimplePassThrough(state, tokenId)
  }
  // execute the step of a intermediate event
  function ExecuteIntermediateEvent(state: State, tokenId: Token.TokenId, eventType: ProcessDefinition.EventType): State { state }

  /**
    * Execute a user task - for testing, we simulate user input
    */
  function {:verify false} ExecuteUserTask(state: ExecutingState, tokenId: Token.TokenId): State
    requires tokenId in GetActiveTokens(state.process.tokenCollection)
    requires tokenId in state.process.tokenCollection.tokens
    requires state.process.tokenCollection.tokens[tokenId].location in state.process.processDefinition.nodes
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

        // Update execution history
        var newHistory := process.executionHistory + [
                            Event(0, token.location, NodeExited, tokenId, Variables.EmptyVariables()),
                            Event(1, nextNodeId, NodeEntered, nextTokenId, Variables.EmptyVariables())
                          ];

        var updatedProcess := Process(
                                processId := process.processId,
                                tokenCollection := tokensWithNext,
                                globalVariables := process.globalVariables,  // 可以在这里更新变量
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
      // Multiple output flows - this is usually an error for UserTask
      BPMNState.Error(process, ValidationError("UserTask should not have multiple outgoing flows"))
  }

  /**
    * Execute a service task - automatic execution
    */
  function {:verify false} ExecuteServiceTask(state: ExecutingState, tokenId: Token.TokenId): State
    requires tokenId in GetActiveTokens(state.process.tokenCollection)
    requires tokenId in state.process.tokenCollection.tokens
    requires state.process.tokenCollection.tokens[tokenId].location in state.process.processDefinition.nodes
  {
    ExecuteSimpleTask(state, tokenId, "ServiceTask")
  }

  /**
    * Execute a manual task - requires human intervention
    */
  function {:verify false} ExecuteManualTask(state: ExecutingState, tokenId: Token.TokenId): State
    requires tokenId in GetActiveTokens(state.process.tokenCollection)
    requires tokenId in state.process.tokenCollection.tokens
    requires state.process.tokenCollection.tokens[tokenId].location in state.process.processDefinition.nodes
  {
    ExecuteSimpleTask(state, tokenId, "ManualTask")
  }

  /**
    * Common task execution logic
    */
  function {:verify false} ExecuteSimpleTask(state: ExecutingState, tokenId: Token.TokenId, taskType: string): State
    requires tokenId in GetActiveTokens(state.process.tokenCollection)
    requires tokenId in state.process.tokenCollection.tokens
    requires state.process.tokenCollection.tokens[tokenId].location in state.process.processDefinition.nodes
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
      state
    else
      ExecuteSimplePassThrough(state, tokenId)
  }

  /**
    * Execute parallel fork
    */
  function ExecuteParallelFork(
    state: ExecutingState,
    tokenId: Token.TokenId,
    outgoingFlows: set<string>
  ): State
    requires CanExecuteParallelFork(state, tokenId, outgoingFlows)
    ensures ExecuteParallelFork(state, tokenId, outgoingFlows).Running?
    ensures var result := ExecuteParallelFork(state, tokenId, outgoingFlows);
            var targetNodes := set flowId | flowId in outgoingFlows ::
                                 state.process.processDefinition.flows[flowId].targetRef;
            forall nodeId :: nodeId in targetNodes ==>
                               exists activeTokenId :: activeTokenId in GetActiveTokens(result.process.tokenCollection) &&
                                                       result.process.tokenCollection.tokens[activeTokenId].location == nodeId
  {
    var process := state.process;
    var token := process.tokenCollection.tokens[tokenId];

    // 消费当前token
    var tokensAfterConsume := Token.ConsumeToken(process.tokenCollection, tokenId);

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

    // 更新执行历史...
    var exitEvent := Event(0, token.location, NodeExited, tokenId, Variables.EmptyVariables());
    var enterEvents := CreateEnterEvents(newTokenIds, outgoingFlows, process.processDefinition.flows);
    var newHistory := process.executionHistory + [exitEvent] + enterEvents;

    var lastExecutedNode := token.location;
    var updatedContext := ExecutionContext.ComputeContext(
                            finalTokens,
                            lastExecutedNode,
                            process.context
                          );

    Running(Process(
              processId := process.processId,
              tokenCollection := finalTokens,
              globalVariables := process.globalVariables,
              processDefinition := process.processDefinition,
              executionHistory := newHistory,
              context := updatedContext
            ))
  }



  /**
    * 为多个流创建tokens
    */
  function CreateTokensForFlows(
    tokens: Token.Collection,
    flows: set<string>,
    flowDefinitions: map<string, ProcessDefinition.SequenceFlow>
  ): (Token.Collection, set<Token.TokenId>)
    requires forall flowId :: flowId in flows ==> flowId in flowDefinitions
    requires ValidTokenCollection(tokens)
    ensures var (finalTokens, newTokenIds) := CreateTokensForFlows(tokens, flows, flowDefinitions);
            // 核心性质：新创建的token数量等于flows数量
            |newTokenIds| == |flows| &&
            // 所有新token都在最终的token集合中且为Active状态
            (forall tokenId :: tokenId in newTokenIds ==>
                                 tokenId in finalTokens.tokens &&
                                 finalTokens.tokens[tokenId].status == Active) &&
            // 新token都不在原始token集合中（唯一性）
            (forall tokenId :: tokenId in newTokenIds ==> tokenId !in tokens.tokens) &&
            // 原有token保持不变
            (forall tokenId :: tokenId in tokens.tokens ==>
                                 tokenId in finalTokens.tokens &&
                                 finalTokens.tokens[tokenId] == tokens.tokens[tokenId]) &&
            // 最终token集合大小 = 原始大小 + 新token数量
            |finalTokens.tokens| == |tokens.tokens| + |flows| &&
            // 保持有效性
            ValidTokenCollection(finalTokens) &&
            // 新增：每个flow的目标节点都有对应的新token
            (forall flowId :: flowId in flows ==>
                                exists tokenId :: tokenId in newTokenIds &&
                                                  finalTokens.tokens[tokenId].location == flowDefinitions[flowId].targetRef &&
                                                  finalTokens.tokens[tokenId].status == Active)
    decreases |flows|
  {
    if |flows| == 0 then
      (tokens, {})
    else
      var flowId := Token.PickOne(flows);
      var remainingFlows := flows - {flowId};
      var targetNodeId := flowDefinitions[flowId].targetRef;
      var (tokensWithNew, newTokenId) := Token.CreateToken(tokens, targetNodeId);

      assert |tokensWithNew.tokens| == |tokens.tokens| + 1;
      assert |remainingFlows| == |flows| - 1;

      var (finalTokens, remainingTokenIds) := CreateTokensForFlows(tokensWithNew, remainingFlows, flowDefinitions);

      assert |remainingTokenIds| == |remainingFlows|;  // 来自递归调用的后置条件
      assert newTokenId !in remainingTokenIds;         // 需要证明或假设

      (finalTokens, remainingTokenIds + {newTokenId})
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
    decreases |tokensToConsume|
  {
    if |tokensToConsume| == 0 then
      tokens
    else
      var tokenId := Token.PickOne(tokensToConsume);
      var remainingTokens := tokensToConsume - {tokenId};
      var tokensAfterOne := Token.ConsumeToken(tokens, tokenId);
      assert forall id :: id in remainingTokens ==>
                            id in tokensAfterOne.tokens && tokensAfterOne.tokens[id].status == Active;

      ConsumeMultipleTokens(tokensAfterOne, remainingTokens)
  }

  /**
    * 简单通过：一进一出
    */
  function ExecuteSimplePassThrough(state: ExecutingState, tokenId: Token.TokenId): State
    requires tokenId in GetActiveTokens(state.process.tokenCollection)
    requires tokenId in state.process.tokenCollection.tokens
    requires state.process.tokenCollection.tokens[tokenId].location in state.process.processDefinition.nodes
  {
    ExecuteSimpleTask(state, tokenId, "Gateway")
  }

  /**
    * 创建进入事件列表
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
} 
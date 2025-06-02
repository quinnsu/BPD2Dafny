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

    // Since RunningProcess constraint, activeTokens is automatically non-empty
    var tokenId := Token.PickOne(activeTokens);
    var process := state.process;
    var token := process.tokenCollection.tokens[tokenId];
    var currentNode := process.processDefinition.nodes[token.location];
    match currentNode.nodeType {
      case StartEvent =>
        if CanExecuteStartEvent(state) then
          ExecuteStartEvent(state)
        else
          state  // or return error state
      case EndEvent => ExecuteEndEvent(state, tokenId)
      case Task(taskType) => ExecuteTask(state, tokenId, taskType)
      case Gateway(gatewayType) => ExecuteGateway(state, tokenId, gatewayType)
      case IntermediateEvent(eventType) => ExecuteIntermediateEvent(state, tokenId, eventType)
    }
  }


  // execute the step of a start event
  function ExecuteStartEvent(state: State): State
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
  {
    state
  }
  // execute the step of a intermediate event
  function ExecuteIntermediateEvent(state: State, tokenId: Token.TokenId, eventType: ProcessDefinition.EventType): State { state }

  /**
    * Execute a user task - for testing, we simulate user input
    */
  function ExecuteUserTask(state: ExecutingState, tokenId: Token.TokenId): State
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
  function ExecuteServiceTask(state: ExecutingState, tokenId: Token.TokenId): State
    requires tokenId in GetActiveTokens(state.process.tokenCollection)
    requires tokenId in state.process.tokenCollection.tokens
    requires state.process.tokenCollection.tokens[tokenId].location in state.process.processDefinition.nodes
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
} 
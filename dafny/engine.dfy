/**
  * Core Execution Engine
  */

include "./token.dfy"
include "./state.dfy"
include "./process.dfy"
include "./utils/variables.dfy"
module ExecutionEngine {
  import opened Token
  import opened BPMNState
  import opened ProcessDefinition
  import opened Variables

  /**
    * The main execution function
    */
  function ExecuteStep(state: State): State
    requires state.Running?
    requires ValidState(state)
    ensures ValidState(ExecuteStep(state))
  {
    var process := state.process;
    var activeTokens := GetActiveTokens(process.tokenCollection);

    if |activeTokens| == 0 then
      Completed(process, process.globalVariables)
    else
      var tokenId := Token.PickOne(activeTokens);
      ExecuteTokenStep(state, tokenId)
  }

  /**
    * Execute the step of a single token
    */
  function ExecuteTokenStep(state: State, tokenId: Token.TokenId): State
    requires state.Running?
    requires tokenId in GetActiveTokens(state.process.tokenCollection)
    requires tokenId in state.process.tokenCollection.tokens
    requires state.process.tokenCollection.tokens[tokenId].location in state.process.processDefinition.nodes
  {
    var process := state.process;
    var token := process.tokenCollection.tokens[tokenId];
    var currentNode := process.processDefinition.nodes[token.location];

    match currentNode.nodeType {
      case StartEvent => ExecuteStartEvent(state, tokenId)
      case EndEvent => ExecuteEndEvent(state, tokenId)
      case Task(taskType) => ExecuteTask(state, tokenId, taskType)
      case Gateway(gatewayType) => ExecuteGateway(state, tokenId, gatewayType)
      case IntermediateEvent(eventType) => ExecuteIntermediateEvent(state, tokenId, eventType)
    }
  }

  // execute the step of a start event
  function ExecuteStartEvent(state: State, tokenId: Token.TokenId): State { state }
  // execute the step of a end event
  function ExecuteEndEvent(state: State, tokenId: Token.TokenId): State { state }
  // execute the step of a task
  function ExecuteTask(state: State, tokenId: Token.TokenId, taskType: TaskType): State { state }
  // execute the step of a gateway
  function ExecuteGateway(state: State, tokenId: Token.TokenId, gatewayType: GatewayType): State { state }
  // execute the step of a intermediate event
  function ExecuteIntermediateEvent(state: State, tokenId: Token.TokenId, eventType: ProcessDefinition.EventType): State { state }
} 
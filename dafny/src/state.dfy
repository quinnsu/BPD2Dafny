/*
 * Provide state type
 */
include "token.dfy"
include "utils/variables.dfy"
include "process.dfy"
include "Context.dfy"
include "utils/option.dfy"

module BPMNState {
  import opened Token
  import opened Variables
  import opened ProcessDefinition
  import opened ExecutionContext
  import opened Optional

  /**
    * error code type
    */
  datatype ErrorCode =
    | ValidationError(message: string)        // 流程定义验证错误
    | RuntimeError(message: string)           // 一般运行时错误
    | TimeoutError(message: string)           // 超时错误
    | ResourceError(message: string)          // 资源错误
    | DeadlockError(details: string)          // 死锁错误
    | ExecutionError(nodeId: string, message: string)  // 节点执行错误
    | FlowError(flowId: string, message: string)       // 流程跳转错误
    | TokenError(tokenId: Token.TokenId, message: string)  // Token相关错误
    | DefinitionError(message: string)                    // 流程定义错误

  /**
    * process object - contains the complete execution context
    */
  datatype ProcessObj = Process(
    processId: string,
    tokenCollection: Token.Collection,
    globalVariables: Variables.VariableMap,
    processDefinition: ProcessDefinition.ProcessDef,
    executionHistory: seq<ExecutionEvent>,
    context: ExecutionContext.Context
  )

  /**
    * BPMN execution state - reference EVM design
    */
  datatype State =
    | NotStarted(processDefinition: ProcessDefinition.ProcessDef, initialVariables: Variables.VariableMap)
    | Running(process: ProcessObj)
    | Completed(process: ProcessObj, output: Variables.VariableMap)
    | Terminated(process: ProcessObj)
    | Error(process: ProcessObj, errorCode: ErrorCode)

  /**
    * wait condition
    */
  datatype WaitCondition =
    | MessageWait(messageType: string)
    | TimerWait(duration: nat)
    | UserTaskWait(taskId: string)
    | ExternalServiceWait(serviceId: string)

  /**
    * execution event record
    */
  datatype ExecutionEvent = Event(
    timestamp: nat,
    nodeId: string,
    eventType: EventType,
    tokenId: Token.TokenId,
    data: Variables.VariableMap
  )

  /**
    * event type
    */
  datatype EventType =
    | NodeEntered
    | NodeExited
    | TokenCreated
    | TokenConsumed
    | VariableUpdated
    | ErrorOccurred

  /**
    * State invariant
    every token must be in the process definition，
    every token in the context queue must be in the token collection and should be active
    every token in the token collection must be in the context queue
    the location of every token must be in the process definition
    */
  predicate ValidState(state: State)
  {
    match state {
      case NotStarted(processDefinition, initialVariables) =>
        ValidProcessDefinition(processDefinition)
      case Running(process) =>
        Token.HasActiveTokens(process.tokenCollection) &&
        Token.ValidTokenCollection(process.tokenCollection) &&
        ValidProcessState(process)
      case Completed(process, _) =>
        !Token.HasActiveTokens(process.tokenCollection) &&
        Token.ValidTokenCollection(process.tokenCollection) &&
        ValidProcessState(process)
      case Terminated(process) =>
        Token.ValidTokenCollection(process.tokenCollection) &&
        ValidProcessState(process)
      case Error(process, _) =>
        true
    }
  }

  predicate ValidProcessState(process: ProcessObj)
  {
    // all active tokens are in the token collection and their location is in the process definition
    (forall tokenId :: tokenId in GetActiveTokens(process.tokenCollection) ==>
                        tokenId in process.tokenCollection.tokens &&
                        process.tokenCollection.tokens[tokenId].location in process.processDefinition.nodes) &&
    (forall tokenId :: tokenId in process.context.executionQueue ==>
                        tokenId in process.tokenCollection.tokens &&
                        process.tokenCollection.tokens[tokenId].status == Active) &&
    (forall tokenId :: tokenId in GetActiveTokens(process.tokenCollection) ==>
                        tokenId in process.context.executionQueue) &&
    ExecutionContext.ValidContext(process.context)
  }

  /**
    * validate process definition
    */
  predicate ValidProcessDefinition(processDefinition: ProcessDefinition.ProcessDef)
  {
    // at least one start node
    |processDefinition.startNodes| > 0 &&
    // at least one end node
    |processDefinition.endNodes| > 0 &&
    // start nodes are in the node collection
    (forall nodeId :: nodeId in processDefinition.startNodes ==> nodeId in processDefinition.nodes) &&
    // end nodes are in the node collection
    (forall nodeId :: nodeId in processDefinition.endNodes ==> nodeId in processDefinition.nodes) &&
    // all flow source and target nodes exist
    (forall flowId :: flowId in processDefinition.flows ==>
                        var flow := processDefinition.flows[flowId];
                        flow.sourceRef in processDefinition.nodes && flow.targetRef in processDefinition.nodes) &&
    // all outgoing flows are in the flow collection
    (forall nodeId :: nodeId in processDefinition.nodes ==>
                        forall flowId :: flowId in processDefinition.nodes[nodeId].outgoing ==>
                                          flowId in processDefinition.flows) &&
    // all incoming flows are in the flow collection
    (forall nodeId :: nodeId in processDefinition.nodes ==>
                        forall flowId :: flowId in processDefinition.nodes[nodeId].incoming ==>
                                          flowId in processDefinition.flows)
  }

  /**
    * create initial state
    */
  function CreateInitialState(processDefinition: ProcessDefinition.ProcessDef, initialVariables: Variables.VariableMap): State
    requires ValidProcessDefinition(processDefinition)
    ensures ValidState(CreateInitialState(processDefinition, initialVariables))
  {
    NotStarted(processDefinition, initialVariables)
  }

  /**
    * check if process can complete
    */
  function CanComplete(state: State): bool
    requires state.Running?
  {
    var process := state.process;
    var activeTokens := Token.GetActiveTokens(process.tokenCollection);

    // check if all active tokens are in end nodes
    forall tokenId :: tokenId in activeTokens ==>
                        process.tokenCollection.tokens[tokenId].location in process.processDefinition.endNodes
  }

  /**
    * an executing state must have active tokens
    | is subset type in Dafny
    type TypeName = baseType | constraint
    witness is used to create a simple example of the type, otherwise dafny complains about the type maybe empty
    */
  type ExecutingState = s:State | s.Running? && Token.HasActiveTokens(s.process.tokenCollection)
    witness Running(BPMN_RUNNING_PROCESS_WITNESS)

  /**
    * a terminated state must not have active tokens
    */
  type TerminatedState = s:State | s.Terminated?
    witness Terminated(BPMN_PROCESS_WITNESS)

  /**
    * a completed state must not have active tokens
    */
  type CompletedState = s:State | s.Completed? && !Token.HasActiveTokens(s.process.tokenCollection)
    witness Completed(BPMN_PROCESS_WITNESS, Variables.EmptyVariables())

  /**
    * create a dummy process definition for witness
    */
  function CreateDummyProcessDef(): ProcessDef
  {
    ProcessDefinition(
      id := "dummy",
      name := "dummy",
      nodes := map["start" := ProcessNode("start", "start", StartEvent, {}, {})],
      flows := map[],
      startNodes := {"start"},
      endNodes := {}
    )
  }

  const BPMN_PROCESS_WITNESS : ProcessObj := Process(
                                               processId := "witness",
                                               tokenCollection := Token.Create(),
                                               globalVariables := Variables.EmptyVariables(),
                                               processDefinition := CreateDummyProcessDef(),
                                               executionHistory := [],
                                               context := ExecutionContext.CreateInitialContext()
                                             )

  const BPMN_RUNNING_PROCESS_WITNESS : ProcessObj :=
    var emptyTokens := Token.Create();
    var (tokensWithOne, tokenId) := Token.CreateToken(emptyTokens, "start");
    var consistentContext := ExecutionContext.CreateConsistentContext(tokensWithOne, "start", 0);
    Process(
      processId := "witness",
      tokenCollection := tokensWithOne,
      globalVariables := Variables.EmptyVariables(),
      processDefinition := CreateDummyProcessDef(),
      executionHistory := [],
      context := consistentContext
    )

  /**
    * State utility functions for location tracking
    */

  /**
    * Get all current token locations
    */
  function GetCurrentLocations(state: State): set<string>
    requires state.Running?
    requires Token.ValidTokenCollection(state.process.tokenCollection)
  {
    ExecutionContext.GetCurrentNodes(state.process.tokenCollection)
  }

  /**
    * Get primary location (when single token)
    */
  function GetPrimaryLocation(state: State): Option<string>
    requires state.Running?
  {
    var process := state.process;
    var activeTokens := Token.GetActiveTokens(process.tokenCollection);
    if |activeTokens| == 1 then
      var tokenId := Token.PickOne(activeTokens);
      Some(process.tokenCollection.tokens[tokenId].location)
    else
      None
  }

  /**
    * Check if execution is at specific node
    */
  predicate IsAtNode(state: State, nodeId: string)
    requires state.Running?
    requires Token.ValidTokenCollection(state.process.tokenCollection)
  {
    var currentNodes := ExecutionContext.GetCurrentNodes(state.process.tokenCollection);
    nodeId in currentNodes
  }

  /**
    * Update ProcessObj's context
    */
  function UpdateProcessContext(
    process: ProcessObj,
    lastExecutedNode: string
  ): ProcessObj
    requires Token.ValidTokenCollection(process.tokenCollection)
  {
    var updatedContext := ExecutionContext.CreateConsistentContext(
                            process.tokenCollection,
                            lastExecutedNode,
                            process.context.executionStep
                          );

    Process(
      processId := process.processId,
      tokenCollection := process.tokenCollection,
      globalVariables := process.globalVariables,
      processDefinition := process.processDefinition,
      executionHistory := process.executionHistory,
      context := updatedContext
    )
  }


  function CreateDeadlockError(process: ProcessObj, details: string): State
  {
    State.Error(process, DeadlockError(details))
  }

  function CreateTokenError(process: ProcessObj, tokenId: Token.TokenId, message: string): State
  {
    State.Error(process, TokenError(tokenId, message))
  }

  function CreateExecutionError(process: ProcessObj, nodeId: string, message: string): State
  {
    State.Error(process, ExecutionError(nodeId, message))
  }

  function CreateFlowError(process: ProcessObj, flowId: string, message: string): State
  {
    State.Error(process, FlowError(flowId, message))
  }

  function CreateValidationError(process: ProcessObj, message: string): State
  {
    State.Error(process, ValidationError(message))
  }

  function CreateRuntimeError(process: ProcessObj, message: string): State
  {
    State.Error(process, RuntimeError(message))
  }
}
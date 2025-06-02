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
    | ValidationError(message: string)
    | RuntimeError(message: string)
    | TimeoutError(message: string)
    | ResourceError(message: string)

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
        Token.ValidTokenCollection(process.tokenCollection) &&
        ValidProcessState(process)
    }
  }

  predicate ValidProcessState(process: ProcessObj)
  {
    // all active tokens are in the token collection and their location is in the process definition
    forall tokenId :: tokenId in GetActiveTokens(process.tokenCollection) ==>
                        tokenId in process.tokenCollection.tokens &&
                        process.tokenCollection.tokens[tokenId].location in process.processDefinition.nodes
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
                        flow.sourceRef in processDefinition.nodes && flow.targetRef in processDefinition.nodes)
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
    var (tokensWithOne, tokenId) := Token.CreateToken(emptyTokens, "dummy");
    Process(
      processId := "witness",
      tokenCollection := tokensWithOne,
      globalVariables := Variables.EmptyVariables(),
      processDefinition := CreateDummyProcessDef(),
      executionHistory := [],
      context := ExecutionContext.CreateInitialContext()
    )

  /**
    * State utility functions for location tracking
    */

  /**
    * Get all current token locations
    */
  function GetCurrentLocations(state: State): set<string>
    requires state.Running?
  {
    state.process.context.currentNodes
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
  {
    nodeId in state.process.context.currentNodes
  }

  /**
    * Update ProcessObj's context
    */
  function UpdateProcessContext(
    process: ProcessObj,
    lastExecutedNode: string
  ): ProcessObj
  {
    var updatedContext := ExecutionContext.ComputeContext(
                            process.tokenCollection,
                            lastExecutedNode,
                            process.context
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
}
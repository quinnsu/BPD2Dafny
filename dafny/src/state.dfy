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
    * Data access type for conflict detection
    */
  datatype AccessType = Read | Write

  /**
    * Variable access information
    */
  datatype VariableAccess = VarAccess(
    variable: string,
    accessType: AccessType
  )

  /**
    * Data conflict type
    */
  datatype ConflictType =
    | WriteWriteConflict    
    | ReadWriteConflict    

  /**
    * Data conflict information
    */
  datatype DataConflict = Conflict(
    variable: string,
    conflictType: ConflictType,
    token1: Token.TokenId,
    token2: Token.TokenId
  )

  /**
    * error code type
    */
  datatype ErrorCode =
    | ValidationError(message: string)      
    | RuntimeError(message: string)           
    | TimeoutError(message: string)           
    | ResourceError(message: string)          
    | DeadlockError(details: string)          
    | ExecutionError(nodeId: string, message: string) 
    | FlowError(flowId: string, message: string)      
    | TokenError(tokenId: Token.TokenId, message: string) 
    | DefinitionError(message: string)                   
    | DataConflictError(conflicts: seq<DataConflict>)     

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
    * BPMN execution state 
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
        ValidProcessState(process) &&
        (forall tokenId :: tokenId in GetActiveTokens(process.tokenCollection) ==>
          process.tokenCollection.tokens[tokenId].location in process.processDefinition.endNodes) 
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
                                          flowId in processDefinition.flows) &&
    // default flows must be in outgoing flows
    (forall nodeId :: nodeId in processDefinition.nodes ==>
                        var node := processDefinition.nodes[nodeId];
                        node.defaultFlow.Some? ==> node.defaultFlow.Unwrap() in node.outgoing)
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
      nodes := map["start" := ProcessNode("start", "start", StartEvent, {}, {"flow1"}, None)],
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

  /**
    * Create data conflict error state
    */
  function CreateDataConflictError(process: ProcessObj, conflicts: seq<DataConflict>): State
  {
    State.Error(process, DataConflictError(conflicts))
  }

  /**
    * Create a data conflict
    */
  function CreateDataConflict(
    variable: string,
    access1: AccessType,
    access2: AccessType,
    token1: Token.TokenId,
    token2: Token.TokenId
  ): DataConflict
    requires HasConflict(access1, access2)
  {
    var conflictType := 
      if access1 == Write && access2 == Write then WriteWriteConflict
      else ReadWriteConflict;
    
    Conflict(variable, conflictType, token1, token2)
  }

  /**
    * Check if two access types conflict
    */
  predicate HasConflict(access1: AccessType, access2: AccessType)
  {
    // Write-Write or Read-Write or Write-Read are all conflicts
    access1 == Write || access2 == Write
  }

  /**
    * Check if two variable accesses conflict
    */
  predicate AccessesConflict(access1: VariableAccess, access2: VariableAccess)
  {
    access1.variable == access2.variable && HasConflict(access1.accessType, access2.accessType)
  }

  /**
    * Safety Properties for BPMN Execution
    */

  /**
    * Check if the state is safe (no deadlocks, conflicts, or activity conflicts)
    */
  predicate IsSafe(state: State)
  {
    !DetectDeadlock(state) &&
    !HasDataConflicts(state) &&
    !HasActivityConflicts(state)
  }

  /**
    * Detect deadlock in the current state
    */
  predicate DetectDeadlock(state: State)
  {
    match state {
      case Running(process) =>
        var activeTokens := GetActiveTokens(process.tokenCollection);
        |activeTokens| > 0 && 
        forall tokenId :: tokenId in activeTokens ==>
          !CanExecuteTokenInState(state, tokenId)
      case Completed(_, _) =>
        false  
      case Terminated(_) =>
        false  
      case Error(_, _) =>
        false  
      case NotStarted(_, _) =>
        false  
    }
  }

  /**
    * Check if a token can be executed in the given state (basic version)
    */
  predicate CanExecuteTokenInState(state: State, tokenId: Token.TokenId)
    requires state.Running?
    requires tokenId in state.process.tokenCollection.tokens
  {
    state.process.tokenCollection.tokens[tokenId].status == Active &&
    state.process.tokenCollection.tokens[tokenId].location in state.process.processDefinition.nodes &&
    CanExecuteBasicNode(state, tokenId)
  }

  /**
    * Basic node execution check (simplified version for deadlock detection)
    */
  predicate CanExecuteBasicNode(state: State, tokenId: Token.TokenId)
    requires state.Running?
    requires tokenId in state.process.tokenCollection.tokens
    requires state.process.tokenCollection.tokens[tokenId].location in state.process.processDefinition.nodes
  {
    var process := state.process;
    var token := process.tokenCollection.tokens[tokenId];
    var location := token.location;
    var node := process.processDefinition.nodes[location];

    match node.nodeType {
      case Gateway(ParallelGateway) =>
        if |node.incoming| > 1 then
          // Parallel join: need all incoming tokens
          var tokensAtLocation := GetActiveTokensAtLocation(process.tokenCollection, location);
          |tokensAtLocation| == |node.incoming|
        else
          true  // Parallel fork or simple gateway
      case _ =>
        true  // Other nodes can generally execute immediately
    }
  }

  /**
    * Check for data conflicts in the current state - based on execution queue
    */
  predicate HasDataConflicts(state: State)
  {
    match state {
      case Running(process) =>
        // Check conflicts between tokens in execution queue
        exists token1, token2 :: token1 in process.context.executionQueue && 
          token2 in process.context.executionQueue && token1 != token2 &&
          token1 in process.tokenCollection.tokens && token2 in process.tokenCollection.tokens &&
          process.tokenCollection.tokens[token1].location in process.processDefinition.nodes &&
          process.tokenCollection.tokens[token2].location in process.processDefinition.nodes &&
          HasDataConflictBetweenTokens(state, token1, token2)
      case _ =>
        false 
    }
  }

  /**
    * Check if two tokens have data conflicts
    */
  predicate HasDataConflictBetweenTokens(state: State, token1: Token.TokenId, token2: Token.TokenId)
    requires state.Running?
    requires token1 in state.process.tokenCollection.tokens
    requires token2 in state.process.tokenCollection.tokens
    requires state.process.tokenCollection.tokens[token1].location in state.process.processDefinition.nodes
    requires state.process.tokenCollection.tokens[token2].location in state.process.processDefinition.nodes
  {
    var access1 := GetTokenVariableAccessBasic(state, token1);
    var access2 := GetTokenVariableAccessBasic(state, token2);
    
    exists var1, var2 :: var1 in access1 && var2 in access2 &&
      var1.variable == var2.variable &&
      (var1.accessType == Write || var2.accessType == Write)
  }

  /**
    * Get basic variable access information for a token (simplified version)
    */
  function GetTokenVariableAccessBasic(state: State, tokenId: Token.TokenId): set<VariableAccess>
    requires state.Running?
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
          var readAccess := set varName | varName in taskData.inputVariables :: 
                             VarAccess(varName, Read);
          var writeAccess := set varName | varName in taskData.outputVariables :: 
                              VarAccess(varName, Write);
          readAccess + writeAccess
        else
          {}
      case _ => {}  
    }
  }

  /**
    * Check for activity conflicts - the execution queue contains the same activity, 
    * which may lead to potential safety issues
    */
  predicate HasActivityConflicts(state: State)
  {
    match state {
      case Running(process) =>
        // Check if execution queue contains tokens pointing to the same activity
        exists nodeId :: nodeId in process.processDefinition.nodes &&
          !IsParallelJoinNode(process.processDefinition.nodes[nodeId]) &&
          |set tokenId | tokenId in process.context.executionQueue && 
              tokenId in process.tokenCollection.tokens &&
              process.tokenCollection.tokens[tokenId].location == nodeId| > 1
      case _ =>
        false  
    }
  }

  /**
    * Check if a node is a parallel join node (允许多个token)
    */
  predicate IsParallelJoinNode(node: ProcessDefinition.Node)
  {
    match node.nodeType {
      case Gateway(ParallelGateway) =>
        |node.incoming| > 1  
      case _ =>
        false
    }
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
}
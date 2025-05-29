/*
 *  Provide state type
 */
include "token.dfy"
include "utils/variables.dfy"
include "process.dfy"
module BPMNState {
  import opened Token
  import opened Variables
  import opened ProcessDefinition

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
    executionHistory: seq<ExecutionEvent>
  )

  /**
    * BPMN execution state
    */
  datatype State =
    | Running(process: ProcessObj)
    | Completed(process: ProcessObj, output: Variables.VariableMap)
    | Terminated(process: ProcessObj)
    | Error(process: ProcessObj, errorCode: ErrorCode)
    | Compensating(process: ProcessObj)
    | Waiting(process: ProcessObj, waitingFor: WaitCondition)

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
    state.Running? ==> Token.ValidTokenCollection(state.process.tokenCollection) &&
                       ValidProcessState(state.process)
  }

  predicate ValidProcessState(process: ProcessObj)
  {
    // all active tokens are in the token collection and their location is in the process definition
    forall tokenId :: tokenId in GetActiveTokens(process.tokenCollection) ==>
                        tokenId in process.tokenCollection.tokens &&
                        process.tokenCollection.tokens[tokenId].location in process.processDefinition.nodes
  }
}
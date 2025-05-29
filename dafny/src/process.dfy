/**
  * Process Definition Module
  * 
  */
include "utils/option.dfy"
module ProcessDefinition {
  import opened Optional

  /**
    * Node Type
    */
  datatype NodeType =
    | StartEvent
    | EndEvent
    | Task(taskType: TaskType)
    | Gateway(gatewayType: GatewayType)
    | IntermediateEvent(eventType: EventType)

  /**
    * Task Type
    */
  datatype TaskType =
    | UserTask
    | ServiceTask
    | ScriptTask
    | BusinessRuleTask


  datatype GatewayType =
    | ExclusiveGateway
    | ParallelGateway
    | InclusiveGateway
    | EventBasedGateway


  datatype EventType =
    | MessageEvent
    | TimerEvent
    | SignalEvent
    | ErrorEvent


  datatype Node = ProcessNode(
    id: string,
    name: string,
    nodeType: NodeType,
    incoming: set<string>,
    outgoing: set<string>
  )


  datatype SequenceFlow = Flow(
    id: string,
    sourceRef: string,
    targetRef: string,
    condition: Option<string>
  )


  datatype ProcessDef = ProcessDefinition(
    id: string,
    name: string,
    nodes: map<string, Node>,
    flows: map<string, SequenceFlow>,
    startNodes: set<string>,
    endNodes: set<string>
  )
} 
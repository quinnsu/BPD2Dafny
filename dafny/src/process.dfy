/**
  * Process Definition Module
  * 
  */
include "utils/option.dfy"
module ProcessDefinition {
  import opened Optional

  /**
    * Task data configuration 
    */
  datatype TaskData = TaskDataConfig(
    inputVariables: seq<string>,   
    outputVariables: seq<string>   
  )

  /**
    * Node Type
    */
  datatype NodeType =
    | StartEvent
    | EndEvent
    | Task(taskType: TaskType, data: Option<TaskData>)  
    | Gateway(gatewayType: GatewayType)
    | IntermediateEvent(eventType: EventType)

  /**
    * Task Type
    */
  datatype TaskType =
    | UserTask
    | ServiceTask
    | ManualTask


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
    outgoing: set<string>,
    defaultFlow: Option<string>  
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
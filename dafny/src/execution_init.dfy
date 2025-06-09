/**
  * BPMN Execution Initialization
  */

include "./process.dfy"
include "./token.dfy"
include "./utils/variables.dfy"
include "./state.dfy"
module ExecutionInit {
  import opened BPMNState
  import opened Token
  import opened Variables
  import opened ProcessDefinition

  /**
    * Initialize execution from a validated model 
    * create an empty token collection and create an initial token at the start event
    * return a running state of the process
    */
  function InitializeExecution(processDef: ProcessDef): State
    requires CanStartProcess(processDef)
    requires |processDef.startNodes| == 1
    ensures InitializeExecution(processDef).Running?
    ensures ValidTokenCollection(InitializeExecution(processDef).process.tokenCollection)
    ensures ValidState(InitializeExecution(processDef))
  {
    var emptyTokens := Token.Create();
    assert |Token.GetActiveTokens(emptyTokens)| == 0;
    var startNodeId := PickOneString(processDef.startNodes);
    var (tokensWithStart, startTokenId) := Token.CreateToken(emptyTokens, startNodeId);
    assert |Token.GetActiveTokens(tokensWithStart)| == 1;
    // CreateToken ensures ValidTokenCollection
    assert ValidTokenCollection(tokensWithStart);
    // startNodeId is in nodes (from CanStartProcess)
    assert startNodeId in processDef.nodes;
    // token location is in nodes  
    assert tokensWithStart.tokens[startTokenId].location == startNodeId;
    assert tokensWithStart.tokens[startTokenId].location in processDef.nodes;
    
    var initialContext := ExecutionContext.CreateConsistentContext(
                            tokensWithStart,
                            startNodeId,
                            0
                          );

    var process := Process(
                     processId := "instance-" + processDef.id,
                     tokenCollection := tokensWithStart,
                     globalVariables := Variables.EmptyVariables(),
                     processDefinition := processDef,
                     executionHistory := [],
                     context := initialContext
                   );

    // Debug: verify we have exactly one active token
    var activeTokens := Token.GetActiveTokens(tokensWithStart);
    assert startTokenId in activeTokens;
 

    Running(process)
  }

  function ProcessStartEvent(state: ExecutingState): State
    requires CanExecuteStartEvent(state)
    requires ValidTokenCollection(state.process.tokenCollection)
    requires ValidProcessDefinition(state.process.processDefinition)
    ensures ProcessStartEvent(state).Running?
    ensures ValidState(ProcessStartEvent(state))
  {
    var process := state.process;
    var activeTokens := Token.GetActiveTokens(process.tokenCollection);
    var tokenId := Token.PickOne(activeTokens);
    var tokensAfterConsume := Token.ConsumeToken(process.tokenCollection, tokenId);
    var currentLocation := process.tokenCollection.tokens[tokenId].location;
    var outgoingFlows := process.processDefinition.nodes[currentLocation].outgoing;
    var flowId := Token.PickOne(outgoingFlows);
    var nextNodeId := process.processDefinition.flows[flowId].targetRef;
    
    // 帮助Dafny推理：flowId在flows中，所以targetRef在nodes中
    assert flowId in process.processDefinition.flows;  // 从ValidFlowStructure得出
    assert nextNodeId in process.processDefinition.nodes;  // 从ValidProcessDefinition得出
    
    var (tokensWithNext, nextTokenId) := Token.CreateToken(tokensAfterConsume, nextNodeId);

    // 获取新的active tokens并更新执行队列
    var newActiveTokens := Token.GetActiveTokens(tokensWithNext);
    
    var updatedContext := ExecutionContext.CreateConsistentContext(
                            tokensWithNext,
                            nextNodeId,
                            process.context.executionStep + 1
                          );
    var newProcess := Process(
                        processId := process.processId,
                        tokenCollection := tokensWithNext,
                        globalVariables := process.globalVariables,
                        processDefinition := process.processDefinition,
                        executionHistory := process.executionHistory,
                        context := updatedContext
                      );
    assert ValidProcessState(newProcess);
    
    Running(newProcess)
  }

  /**
    * Helper function to pick one string from a set (similar to PickOne)
    */
  function {:verify false} PickOneString(s: set<string>): string
    requires |s| > 0
  {
    var x :| x in s; x
  }


  predicate CanStartProcess(processDefinition: ProcessDefinition.ProcessDef)
  {
    |processDefinition.startNodes| == 1 &&
    |processDefinition.endNodes| > 0 &&

    // start nodes exist in the nodes map
    (forall startNodeId :: startNodeId in processDefinition.startNodes ==>
                             startNodeId in processDefinition.nodes) &&

    // end nodes exist in the nodes map
    (forall endNodeId :: endNodeId in processDefinition.endNodes ==>
                           endNodeId in processDefinition.nodes) &&

    // start event cannot have incoming flows
    (forall startNodeId :: startNodeId in processDefinition.startNodes ==>
                             processDefinition.nodes[startNodeId].incoming == {}) &&

    // start event must have outgoing flows
    (forall startNodeId :: startNodeId in processDefinition.startNodes ==>
                             |processDefinition.nodes[startNodeId].outgoing| > 0) &&

    // all outgoing flows from start nodes exist in flows map
    (forall startNodeId :: startNodeId in processDefinition.startNodes ==>
                             forall flowId :: flowId in processDefinition.nodes[startNodeId].outgoing ==>
                                                flowId in processDefinition.flows) &&

    // end event cannot have outgoing flows
    (forall endNodeId :: endNodeId in processDefinition.endNodes ==>
                           processDefinition.nodes[endNodeId].outgoing == {})
  }

  /**
    * 验证状态是否可以执行StartEvent
    */
  predicate CanExecuteStartEvent(state: State)
  {
    state.Running? &&
    Token.HasActiveTokens(state.process.tokenCollection) &&
    ValidProcessDefinition(state.process.processDefinition) &&
    ValidStartEventExecution(state.process)
  }

  /**
    * 验证流程对象是否满足StartEvent执行条件
    */
  predicate ValidStartEventExecution(process: ProcessObj)
  {
    |process.processDefinition.startNodes| == 1 &&
    ValidActiveTokensAtStart(process) &&
    ValidFlowStructure(process)
  }

  /**
    * 验证活跃token是否都在开始节点且有效
    */
  predicate ValidActiveTokensAtStart(process: ProcessObj)
  {
    forall tokenId :: tokenId in Token.GetActiveTokens(process.tokenCollection) ==>
                        tokenId in process.tokenCollection.tokens &&
                        process.tokenCollection.tokens[tokenId].location in process.processDefinition.startNodes &&
                        process.tokenCollection.tokens[tokenId].location in process.processDefinition.nodes
  }

  /**
    * 验证流结构的有效性
    */
  predicate ValidFlowStructure(process: ProcessObj)
  {
    forall tokenId :: tokenId in Token.GetActiveTokens(process.tokenCollection) ==>
                        var location := process.tokenCollection.tokens[tokenId].location;
                        location in process.processDefinition.nodes &&
                        |process.processDefinition.nodes[location].outgoing| > 0 &&
                        (forall flowId :: flowId in process.processDefinition.nodes[location].outgoing ==>
                                            flowId in process.processDefinition.flows)
  }

  /**
    * 验证token是否可以在其当前位置执行
    */
  predicate CanExecuteToken(state: State, tokenId: TokenId)
    requires state.Running?
    requires tokenId in state.process.tokenCollection.tokens
  {
    var token := state.process.tokenCollection.tokens[tokenId];
    var location := token.location;

    location in state.process.processDefinition.nodes &&
    (var node := state.process.processDefinition.nodes[location];
     match node.nodeType {
       case StartEvent => CanExecuteStartEvent(state)
       case EndEvent => true  // EndEvent通常没有复杂前置条件
       case Task(_) => true
       case Gateway(_) => true
       case IntermediateEvent(_) => true
     })
  }

} 
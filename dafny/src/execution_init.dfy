/**
  * BPMN Execution Initialization
  */
include "engine.dfy"
include "./process.dfy"
module ExecutionInit {
  import opened ExecutionEngine
  import opened BPMNState
  import opened Token
  import opened Variables
  import opened ProcessDefinition

  /**
    * Initialize execution from a validated model 
    * create an empty token collection and create an initial token at the first start event
    * return a running state of the process
    */
  function InitializeExecution(processDef: ProcessDef): State
    requires |processDef.startNodes| > 0
  {
    // Create empty token collection
    var emptyTokens := Token.Create();

    // Create initial token at the first start event
    var startNodeId := PickOneString(processDef.startNodes);
    var (tokensWithStart, startTokenId) := Token.CreateToken(emptyTokens, startNodeId);

    // Create initial process object
    var process := Process(
                     processId := "instance-" + processDef.id,
                     tokenCollection := tokensWithStart,
                     globalVariables := Variables.EmptyVariables(),
                     processDefinition := processDef,
                     executionHistory := []
                   );

    Running(process)
  }

  /**
    * Helper function to pick one string from a set (similar to PickOne)
    */
  function {:verify false} PickOneString(s: set<string>): string
    requires |s| > 0
  {
    var x :| x in s; x
  }

} 
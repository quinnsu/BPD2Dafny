/*
 * Simple tests for direct ProcessDefinition
 */
include "json_model.dfy"
include "../src/execution_init.dfy"
include "../src/engine.dfy"

module TestSimple {
  import opened JsonModel
  import opened ExecutionInit
  import opened BPMNState
  import opened ExecutionEngine

  /**
    * Test: Basic model validation
    */
  function TestBasicValidation(): bool
  {
    var processDef := CreateParsedModel01();
    |processDef.startNodes| > 0 && |processDef.endNodes| > 0
  }

  /**
    * Test: Initialize and run
    */
  function TestInitializeAndRun(): bool
  {
    var processDef := CreateParsedModel01();
    var initialState := InitializeExecution(processDef);
    initialState.Running?
  }

  /**
    * Test: Start process
    */
  function TestStartProcess(): bool
  {
    var processDef := CreateParsedModel01();
    var initialState := InitializeExecution(processDef);
    initialState.Running?
  }

  method TestExecuteStartEventFrom01()
  {
    var processDef := CreateParsedModel01();
    var initialState := InitializeExecution(processDef);
    var nextState := ExecuteStep(initialState);
    assert nextState.Running?;
  }

  method TestCompleteModel01Execution()
  {
    var processDef := CreateParsedModel01();
    var state0 := InitializeExecution(processDef);

    var state1 := ExecuteStep(state0);              // StartEvent → t0
    assert state1.Running?;
    assert IsAtNode(state1, "t0");                  // 验证在t0节点

    var state2 := ExecuteStep(state1);              // t0 → ParallelGateway_05lp38c
    assert state2.Running?;
    assert IsAtNode(state2, "ParallelGateway_05lp38c");
  }

  /**
    * Execute multiple steps for testing
   
  function ExecuteMultipleSteps(initialState: State, maxSteps: nat): State
    requires initialState.Running?
    decreases maxSteps
  {
    if maxSteps == 0 then
      initialState
    else
      match initialState {
        case Running(process) =>
          if Token.HasActiveTokens(process.tokenCollection) then
            var nextState := ExecuteStep(initialState);
            match nextState {
              case Running(_) => ExecuteMultipleSteps(nextState, maxSteps - 1)
              case Completed(_, _) => nextState
              case _ => nextState  // Error, Terminated等
            }
          else
            // 没有活跃token，应该转为Completed
            Completed(process, process.globalVariables)
        case _ => initialState
      }
  } */
} 
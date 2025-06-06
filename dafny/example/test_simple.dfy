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
  import opened Token

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

  /**
    * 调试辅助函数：检查特定位置是否有token
    */
  predicate HasTokenAt(state: State, nodeId: string)
    requires state.Running?
  {
    exists tokenId :: tokenId in state.process.tokenCollection.tokens &&
                      state.process.tokenCollection.tokens[tokenId].location == nodeId &&
                      state.process.tokenCollection.tokens[tokenId].status == Active
  }

  /**
    * 获取所有活跃token的位置
    */
  function GetAllActiveLocations(state: State): set<string>
    requires state.Running?
  {
    set tokenId | tokenId in GetActiveTokens(state.process.tokenCollection) ::
      state.process.tokenCollection.tokens[tokenId].location
  }

  /**
    * 计算活跃token数量
    */
  function CountActiveTokens(state: State): nat
    requires state.Running?
  {
    |GetActiveTokens(state.process.tokenCollection)|
  }

  /**
    * 详细的测试方法，包含更多验证
    */
  method{:timeLimit 60} TestCompleteModel01ExecutionDetailed()
  {
    var processDef := CreateParsedModel01();
    var state0 := InitializeExecution(processDef);

    // 验证初始状
    assert state0.Running?;

    var state1 := ExecuteStep(state0);              // StartEvent → t0
    assert state1.Running?;
    assert IsAtNode(state1, "t0");

    var state2 := ExecuteStep(state1);              // t0 → ParallelGateway_05lp38c
    assert state2.Running?;
    assert IsAtNode(state2, "ParallelGateway_05lp38c");

    var state3 := ExecuteStep(state2);              // ParallelGateway -> tdown, tup
    assert state3.Running?;
    assert IsAtNode(state3, "tdown") && IsAtNode(state3, "tup");
    //assert CountActiveTokens(state3) == 2;
    //parallerlGateway join

  
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
/*
 * Simple tests for direct ProcessDefinition
 */
include "json_model.dfy"
include "../src/execution_init.dfy"
include "../src/engine.dfy"
include "../src/scheduling.dfy"

module TestSimple {
  import opened JsonModel
  import opened ExecutionInit
  import opened BPMNState
  import opened ExecutionEngine
  import opened Token
  import opened Scheduling

  /**
    * Test: Basic model validation
    */
  function {:verify false} TestBasicValidation(): bool
  {
    var processDef := CreateParsedModel01();
    |processDef.startNodes| > 0 && |processDef.endNodes| > 0
  }

  /**
    * Test: Initialize and run
    */
  function {:verify false} TestInitializeAndRun(): bool
  {
    var processDef := CreateParsedModel01();
    var initialState := InitializeExecution(processDef);
    initialState.Running?
  }

  /**
    * Test: Start process
    */
  function {:verify false} TestStartProcess(): bool
  {
    var processDef := CreateParsedModel01();
    var initialState := InitializeExecution(processDef);
    initialState.Running?
  }

  method {:verify false} TestExecuteStartEventFrom01()
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

 
  function {:verify false} GetAllActiveLocations(state: State): set<string>
    requires state.Running?
  {
    set tokenId | tokenId in GetActiveTokens(state.process.tokenCollection) ::
      state.process.tokenCollection.tokens[tokenId].location
  }

  function {:verify false} CountActiveTokens(state: State): nat
    requires state.Running?
  {
    |GetActiveTokens(state.process.tokenCollection)|
  }


  method{:verify false} TestCompleteModel01ExecutionStep()

  {
    var processDef := CreateParsedModel01();
    var state0 := InitializeExecution(processDef);

    // 验证初始状
    assert state0.Running?;
    //use ExecuteStep to display one step
    var state1 := ExecuteStep(state0);
    assert state1.Running?;
    assert IsAtNode(state1, "t0");
    var state2 := ExecuteStep(state1);              // t0 → ParallelGateway_05lp38c
    assert state2.Running?;
    assert IsAtNode(state2, "ParallelGateway_05lp38c");
    var state3 := ExecuteStep(state2);              // ParallelGateway -> tdown, tup
    assert state3.Running?;
    assert IsAtNode(state3, "tdown") && IsAtNode(state3, "tup");
    var state4 := ExecuteStep(state3);              // tdown → ParallelGateway_0vffee4
    assert state4.Running?;
    assert IsAtNode(state4, "ParallelGateway_0vffee4");
 
  }
 
  method TestSimpleLinearProcess()
  {
    var processDef := CreateSimpleLinearProcess();
    var state0 := InitializeExecution(processDef);
    var state1 := ExecuteStep(state0);
    assert state1.Running?;
    assert IsAtNode(state1, "task");
    var state2 := ExecuteStep(state1);
    assert state2.Running?;
    assert IsAtNode(state2, "end"); 
    var state3 := ExecuteStep(state2);
    assert state3.Completed?;
  }

  method {:verify false} TestModel01Execution()
    decreases *
  {
    var processDef := CreateParsedModel01();
    var state0 := InitializeExecution(processDef);
    Execute(state0);              // StartEvent → t0
  }


  method {:verify false}{:isolate_assertions} TestSimpleParallelProcess()
  {
    var processDef := CreateDirectParallelProcess();
    var state0 := InitializeExecution(processDef);
     
    // Step 1: StartEvent -> ParallelFork
    var state1 := ExecuteStep(state0);
    var activeTokens := GetActiveTokens(state1.process.tokenCollection);
    assert |activeTokens| == 1;
    assert state1.Running?;
    assert IsAtNode(state1, "ParallelFork");
    
    // Step 2: ParallelFork -> ParallelJoin (应该创建2个token)
    // 使用lemma帮助验证ParallelFork的效果
    var tokenAtFork := Token.PickOne(activeTokens);
    var outgoingFlows := {"flow_fork_join1", "flow_fork_join2"};
    ParallelForkCreatesExactTokens(state1, tokenAtFork, outgoingFlows);
    var state2 := ExecuteStep(state1);
    var activeTokens2 := GetActiveTokens(state2.process.tokenCollection);
    assert |activeTokens2| == 2; //can pass
    assert state2.Running?;// Can pass 
    assert exists tokenId :: tokenId in state2.process.tokenCollection.tokens && 
                              state2.process.tokenCollection.tokens[tokenId].location == "ParallelJoin" by {
      ParallelForkCreatesTokensAtTargetLocations(state1, tokenAtFork, outgoingFlows);
    }
    //assert state2.process.tokenCollection.tokens[tokenId2].location == "ParallelJoin";
    //assert ExecutionContext.GetCurrentNodes(state2.process.tokenCollection) == {"ParallelJoin"};

    //var state3 := ExecuteStep(state2);
    //assert state3.Running?;
    //assert IsAtNode(state3, "ParallelJoin"); 
    //var state4 := ExecuteStep(state3);
    //assert state4.Running?;
    //assert IsAtNode(state4, "EndEvent_1");
 
  }
  method{:verify false} CanComplete(traces: Trace, schedule: Schedule, initialState: State)
  requires FairSchedule(schedule, traces)
  ensures exists n :: traces(n).Completed?
{
   var n := ProcessEventuallyCompletes(traces, schedule, 0);
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
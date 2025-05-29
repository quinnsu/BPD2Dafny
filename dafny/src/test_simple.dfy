/*
 * Simple tests for direct ProcessDefinition
 */
include "json_model.dfy"
include "execution_init.dfy"

module TestSimple {
  import opened JsonModel
  import opened ExecutionInit
  import opened BPMNState

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
} 
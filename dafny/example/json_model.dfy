/**
  * Direct JSON to ProcessDefinition conversion
  */
include "process.dfy"
include "utils/option.dfy"

module JsonModel {
  import opened ProcessDefinition
  import opened Optional

  /**
    * Python script generates this function directly
    */
  function CreateParsedModel01(): ProcessDef
  {
    var nodes := map[
                   "StartEvent_1" := ProcessNode("StartEvent_1", "Start", StartEvent, {}, {"t0"}),
                   "EndEvent_16dmtu6" := ProcessNode("EndEvent_16dmtu6", "End", EndEvent, {"ExclusiveGateway_0ms7zfc"}, {}),
                   "t0" := ProcessNode("t0", "Which option?", Task(UserTask), {"StartEvent_1"}, {"ParallelGateway_05lp38c"}),
                   "tup" := ProcessNode("tup", "Up", Task(UserTask), {"ParallelGateway_05lp38c"}, {"ParallelGateway_0vffee4"}),
                   "tdown" := ProcessNode("tdown", "Down", Task(UserTask), {"ParallelGateway_05lp38c"}, {"ParallelGateway_0vffee4"}),
                   "ParallelGateway_05lp38c" := ProcessNode("ParallelGateway_05lp38c", "Split", Gateway(ParallelGateway), {"t0"}, {"tup", "tdown"}),
                   "ParallelGateway_0vffee4" := ProcessNode("ParallelGateway_0vffee4", "Join", Gateway(ParallelGateway), {"tup", "tdown"}, {"mt"}),
                   "ExclusiveGateway_0ms7zfc" := ProcessNode("ExclusiveGateway_0ms7zfc", "Merge", Gateway(ExclusiveGateway), {"tup2", "tdown2"}, {"EndEvent_16dmtu6"})
                 ];

    var flows := map[
                   "flow_start_t0" := Flow("flow_start_t0", "StartEvent_1", "t0", None),
                   "flow_t0_split" := Flow("flow_t0_split", "t0", "ParallelGateway_05lp38c", None),
                   "flow_split_up" := Flow("flow_split_up", "ParallelGateway_05lp38c", "tup", None),
                   "flow_split_down" := Flow("flow_split_down", "ParallelGateway_05lp38c", "tdown", None),
                   "flow_up_join" := Flow("flow_up_join", "tup", "ParallelGateway_0vffee4", None),
                   "flow_down_join" := Flow("flow_down_join", "tdown", "ParallelGateway_0vffee4", None),
                   "flow_join_end" := Flow("flow_join_end", "ExclusiveGateway_0ms7zfc", "EndEvent_16dmtu6", None)
                 ];

    ProcessDefinition(
      id := "Process_1804ck9",
      name := "Process 01",
      nodes := nodes,
      flows := flows,
      startNodes := {"StartEvent_1"},
      endNodes := {"EndEvent_16dmtu6"}
    )
  }
} 
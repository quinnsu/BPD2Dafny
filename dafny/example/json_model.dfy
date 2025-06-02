/**
  * Direct JSON to ProcessDefinition conversion
  */
include "../src/process.dfy"
include "../src/utils/option.dfy"

module JsonModel {
  import opened ProcessDefinition
  import opened Optional

  /**
    * Python script generates this function directly
    */
  function CreateParsedModel01(): ProcessDef
    ensures |CreateParsedModel01().startNodes| == 1
    ensures |CreateParsedModel01().endNodes| > 0
    ensures forall startNodeId :: startNodeId in CreateParsedModel01().startNodes ==>
                                    startNodeId in CreateParsedModel01().nodes
    ensures forall endNodeId :: endNodeId in CreateParsedModel01().endNodes ==>
                                  endNodeId in CreateParsedModel01().nodes
    ensures forall startNodeId :: startNodeId in CreateParsedModel01().startNodes ==>
                                    CreateParsedModel01().nodes[startNodeId].incoming == {}

  {
    var nodes := map[
                   "StartEvent_1" := ProcessNode("StartEvent_1", "Start", StartEvent, {}, {"flow_start_t0"}),
                   "EndEvent_16dmtu6" := ProcessNode("EndEvent_16dmtu6", "End", EndEvent, {"ExclusiveGateway_0ms7zfc"}, {}),
                   "t0" := ProcessNode("t0", "Which option?", Task(UserTask), {"flow_start_t0"}, {"flow_t0_split"}),
                   "tup" := ProcessNode("tup", "Up", Task(UserTask), {"flow_t0_split"}, {"flow_split_up"}),
                   "tdown" := ProcessNode("tdown", "Down", Task(UserTask), {"flow_t0_split"}, {"flow_split_down"}),
                   "ParallelGateway_05lp38c" := ProcessNode("ParallelGateway_05lp38c", "Split", Gateway(ParallelGateway), {"flow_t0_split"}, {"flow_split_up", "flow_split_down"}),
                   "ParallelGateway_0vffee4" := ProcessNode("ParallelGateway_0vffee4", "Join", Gateway(ParallelGateway), {"flow_split_up", "flow_split_down"}, {"flow_up_join", "flow_down_join"}),
                   "ExclusiveGateway_0ms7zfc" := ProcessNode("ExclusiveGateway_0ms7zfc", "Merge", Gateway(ExclusiveGateway), {"flow_up_join", "flow_down_join"}, {"flow_join_end"})
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
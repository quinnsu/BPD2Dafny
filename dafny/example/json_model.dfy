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
                   "StartEvent_1" := ProcessNode("StartEvent_1", "Start", StartEvent, {}, {"flow_start_t0"}, None),
                   "EndEvent_16dmtu6" := ProcessNode("EndEvent_16dmtu6", "End", EndEvent, {"ExclusiveGateway_0ms7zfc"}, {}, None),
                   "t0" := ProcessNode("t0", "Which option?", Task(UserTask, None), {"flow_start_t0"}, {"flow_t0_split"}, None),
                   "tup" := ProcessNode("tup", "Up", Task(UserTask, None), {"flow_t0_split"}, {"flow_split_up"}, None),
                   "tdown" := ProcessNode("tdown", "Down", Task(UserTask, None), {"flow_t0_split"}, {"flow_split_down"}, None),
                   "ParallelGateway_05lp38c" := ProcessNode("ParallelGateway_05lp38c", "Split", Gateway(ParallelGateway), {"flow_t0_split"}, {"flow_split_up", "flow_split_down"}, None),
                   "ParallelGateway_0vffee4" := ProcessNode("ParallelGateway_0vffee4", "Join", Gateway(ParallelGateway), {"flow_split_up", "flow_split_down"}, {"flow_up_join", "flow_down_join"}, None),
                   "ExclusiveGateway_0ms7zfc" := ProcessNode("ExclusiveGateway_0ms7zfc", "Merge", Gateway(ExclusiveGateway), {"flow_up_join", "flow_down_join"}, {"flow_join_end"}, Some("flow_join_end"))
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

  function CreateSimpleLinearProcess(): ProcessDef
{
    ProcessDefinition(
        id := "linear",
        name := "Simple Linear Process",
        nodes := map[
            "start" := ProcessNode("start", "Start", StartEvent, {}, {"flow1"}, None),
            "task" := ProcessNode("task", "User Task", Task(UserTask, None), {"flow1"}, {"flow2"}, None),
            "end" := ProcessNode("end", "End", EndEvent, {"flow2"}, {}, None)
        ],
        flows := map[
            "flow1" := Flow("flow1", "start", "task", None),
            "flow2" := Flow("flow2", "task", "end", None)
        ],
        startNodes := {"start"},
        endNodes := {"end"}
    )
}

  /** 
    * 简单的并行网关示例：fork-join模式
    * 流程结构: StartEvent → ParallelFork → [Task1, Task2] → ParallelJoin → EndEvent
    */
  function CreateSimpleParallelProcess(): ProcessDef
    ensures |CreateSimpleParallelProcess().startNodes| == 1
    ensures |CreateSimpleParallelProcess().endNodes| == 1
    ensures forall startNodeId :: startNodeId in CreateSimpleParallelProcess().startNodes ==>
                                    startNodeId in CreateSimpleParallelProcess().nodes
    ensures forall endNodeId :: endNodeId in CreateSimpleParallelProcess().endNodes ==>
                                  endNodeId in CreateSimpleParallelProcess().nodes
    ensures forall startNodeId :: startNodeId in CreateSimpleParallelProcess().startNodes ==>
                                    CreateSimpleParallelProcess().nodes[startNodeId].incoming == {}
  {
    var nodes := map[
                   "StartEvent_1" := ProcessNode("StartEvent_1", "开始", StartEvent, {}, {"flow_start_fork"}, None),
                   "ParallelFork" := ProcessNode("ParallelFork", "并行分叉", Gateway(ParallelGateway), {"flow_start_fork"}, {"flow_fork_task1", "flow_fork_task2"}, None),
                   "Task1" := ProcessNode("Task1", "任务1", Task(UserTask, None), {"flow_fork_task1"}, {"flow_task1_join"}, None),
                   "Task2" := ProcessNode("Task2", "任务2", Task(UserTask, None), {"flow_fork_task2"}, {"flow_task2_join"}, None),
                   "ParallelJoin" := ProcessNode("ParallelJoin", "并行合并", Gateway(ParallelGateway), {"flow_task1_join", "flow_task2_join"}, {"flow_join_end"}, None),
                   "EndEvent_1" := ProcessNode("EndEvent_1", "结束", EndEvent, {"flow_join_end"}, {}, None)
                 ];

    var flows := map[
                   "flow_start_fork" := Flow("flow_start_fork", "StartEvent_1", "ParallelFork", None),
                   "flow_fork_task1" := Flow("flow_fork_task1", "ParallelFork", "Task1", None),
                   "flow_fork_task2" := Flow("flow_fork_task2", "ParallelFork", "Task2", None),
                   "flow_task1_join" := Flow("flow_task1_join", "Task1", "ParallelJoin", None),
                   "flow_task2_join" := Flow("flow_task2_join", "Task2", "ParallelJoin", None),
                   "flow_join_end" := Flow("flow_join_end", "ParallelJoin", "EndEvent_1", None)
                 ];

    ProcessDefinition(
      id := "SimpleParallel_001",
      name := "简单并行流程",
      nodes := nodes,
      flows := flows,
      startNodes := {"StartEvent_1"},
      endNodes := {"EndEvent_1"}
         )
   }

  /**
    * 直接的并行网关示例：fork直接连接join
    * 流程结构: StartEvent → ParallelFork → ParallelJoin → EndEvent
    * 验证并行网关可以直接连接而无需中间任务
    */
  function CreateDirectParallelProcess(): ProcessDef
    ensures |CreateDirectParallelProcess().startNodes| == 1
    ensures |CreateDirectParallelProcess().endNodes| == 1
    ensures forall startNodeId :: startNodeId in CreateDirectParallelProcess().startNodes ==>
                                    startNodeId in CreateDirectParallelProcess().nodes
    ensures forall endNodeId :: endNodeId in CreateDirectParallelProcess().endNodes ==>
                                  endNodeId in CreateDirectParallelProcess().nodes
    ensures forall startNodeId :: startNodeId in CreateDirectParallelProcess().startNodes ==>
                                    CreateDirectParallelProcess().nodes[startNodeId].incoming == {}
  {
    var nodes := map[
                   "StartEvent_1" := ProcessNode("StartEvent_1", "开始", StartEvent, {}, {"flow_start_fork"}, None),
                   "ParallelFork" := ProcessNode("ParallelFork", "并行分叉", Gateway(ParallelGateway), {"flow_start_fork"}, {"flow_fork_join1", "flow_fork_join2"}, None),
                   "ParallelJoin" := ProcessNode("ParallelJoin", "并行合并", Gateway(ParallelGateway), {"flow_fork_join1", "flow_fork_join2"}, {"flow_join_end"}, None),
                   "EndEvent_1" := ProcessNode("EndEvent_1", "结束", EndEvent, {"flow_join_end"}, {}, None)
                 ];

    var flows := map[
                   "flow_start_fork" := Flow("flow_start_fork", "StartEvent_1", "ParallelFork", None),
                   "flow_fork_join1" := Flow("flow_fork_join1", "ParallelFork", "ParallelJoin", None),
                   "flow_fork_join2" := Flow("flow_fork_join2", "ParallelFork", "ParallelJoin", None),
                   "flow_join_end" := Flow("flow_join_end", "ParallelJoin", "EndEvent_1", None)
                 ];

    ProcessDefinition(
      id := "DirectParallel_001",
      name := "直接并行流程",
      nodes := nodes,
      flows := flows,
      startNodes := {"StartEvent_1"},
      endNodes := {"EndEvent_1"}
    )
  }

  /**
    * 带数据变量的简单线性流程示例
    */
  function CreateProcessWithData(): ProcessDef
  {
    var userTaskData := TaskDataConfig(
      inputVariables := ["orderId", "customerName"],
      outputVariables := ["approved", "comments"]
    );

    var serviceTaskData := TaskDataConfig(
      inputVariables := ["approved", "orderId"],
      outputVariables := ["processResult", "timestamp"]
    );

    ProcessDefinition(
      id := "data-process", 
      name := "Process with Data Variables",
      nodes := map[
        "start" := ProcessNode("start", "Start", StartEvent, {}, {"flow1"}, None),
        "userTask" := ProcessNode("userTask", "Review Order", Task(UserTask, Some(userTaskData)), {"flow1"}, {"flow2"}, None),
        "serviceTask" := ProcessNode("serviceTask", "Update System", Task(ServiceTask, Some(serviceTaskData)), {"flow2"}, {"flow3"}, None),
        "end" := ProcessNode("end", "End", EndEvent, {"flow3"}, {}, None)
      ],
      flows := map[
        "flow1" := Flow("flow1", "start", "userTask", None),
        "flow2" := Flow("flow2", "userTask", "serviceTask", None),
        "flow3" := Flow("flow3", "serviceTask", "end", None)
      ],
      startNodes := {"start"},
      endNodes := {"end"}
    )
  }
 }  
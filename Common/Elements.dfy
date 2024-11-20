module Basic_Elements {
datatype Operator = Sequence | Parallel | Exclusive | Loop
datatype Node =
  | OperatorNode(op: Operator, left: Node, right: Node)
  | TaskNode(key: string, writeVariable: set<string>, readVariable: set<string>)
  | ConditionNode()

}

//Empty只会在特殊情况下用到，如只有一个任务
//ConditionNode还没有写具体的实现

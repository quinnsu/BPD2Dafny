module Basic_Elements {
datatype Operator = Sequence | Parallel | Exclusive | Loop
datatype Node =
  | OperatorNode(op: Operator, left: Node, right: Node)
  | TaskNode(key: string, writeVariable: set<string>, readVariable: set<string>)
  | ConditionNode()

}


include "./Elements.dfy"
include "../Proof/Proofs.dfy"

module Properties{

  import opened Basic_Elements
  import opened Proofs

  //Incosistent Data Check

  datatype IDValidationResult = Valid(writeVars: set<string>, readVars: set<string>) | Invalid( WRC: set<string>, WWC: set<string>)

  //Check ID

  function CheckID(node: Node) : (result : IDValidationResult)
    ensures node.TaskNode? ==> result.Valid?
    ensures result.Invalid? ==> (result.WRC != {} || result.WWC != {})
    decreases node
  {
    match node
    {
      case OperatorNode (op,left,right) =>
        match op{

          case Parallel =>
            var leftResult := CheckID(left);
            if leftResult.Invalid? then
              leftResult
            else
              var rightResult := CheckID(right);
              if rightResult.Invalid? then
                rightResult
              else

                var leftWriteRightReadConflict := leftResult.writeVars * rightResult.readVars;
                var rightWriteLeftReadConflict := rightResult.writeVars * leftResult.readVars;
                var writeWriteConflict := leftResult.writeVars * rightResult.writeVars;

                var allConflicts := leftWriteRightReadConflict + rightWriteLeftReadConflict + writeWriteConflict;

                if |allConflicts| > 0 then
                  IDValidationResult.Invalid(leftWriteRightReadConflict+rightWriteLeftReadConflict, writeWriteConflict)
                else
                  IDValidationResult.Valid(
                    leftResult.writeVars + rightResult.writeVars,
                    leftResult.readVars + rightResult.readVars
                  )


          case Sequence =>
            //SequenceIDLemma1(node);
            var leftResult := CheckID(left);
            if leftResult.Invalid? then
              leftResult
            else
              var rightResult := CheckID(right);
              if rightResult.Invalid? then
                rightResult
              else
                IDValidationResult.Valid(
                  leftResult.writeVars + rightResult.writeVars,
                  leftResult.readVars + rightResult.readVars
                )

          case Exclusive =>
            CheckID(left)

          case Loop =>
            CheckID(right)
        }
      case Empty =>
        IDValidationResult.Valid({},{})

      case TaskNode(_,writeVariable,readVariable) =>
        IDValidationResult.Valid(writeVariable,readVariable)
      case ConditionNode() =>
        IDValidationResult.Valid({},{})

    }
  }

  //检查 Missing Data

  datatype MDValidationResult = Valid | Invalid(node: Node, missingVar: set<string>)


  function CheckMD(node: Node) :(result : MDValidationResult)
    requires MPST(node)
  {
    var (resultVars, validationResult):=  MDTraversal(node, node,{});
    validationResult
  }

  /* node: the current node
    curVars: the write vars when entering this node
    result.0: the write vars when leaving this node */
  function MDTraversal(tree: Node,node: Node, curVars: set<string>) :(result: (set<string>, MDValidationResult))
    decreases node
    requires MPST(node) && MPST(tree)
    requires node_in_tree(tree,node)
    requires IsMDInitialState(tree,node,curVars)
    ensures MPST(node) ==> curVars <= result.0
    ensures node.TaskNode? && result.1.Valid? ==> node.readVariable <= curVars
    ensures node.TaskNode? && result.1.Invalid? ==>  exists x :: x in node.readVariable && x !in curVars
    ensures node.TaskNode? ==> node.writeVariable <= result.0
    ensures IsMDInitialState(tree,node,curVars)
    // all the write variables of task nodes in a tree are updated as the result
    ensures MPST(node) && result.1.Valid? ==> forall x :: x in writeVars_task_nodes(node) ==>  x in result.0

  {
    match node
    {


      case TaskNode(_,definedVariable,readVariable) =>
        if readVariable <= curVars then
          (curVars + definedVariable, MDValidationResult.Valid)
        else
          (curVars + definedVariable, MDValidationResult.Invalid(node, readVariable))
      case OperatorNode(op,left,right) =>
        assert (node_in_tree(tree,left)) by {NodeLemma2(tree,node);}
        NodeLemma(tree,node);
        match op{
          case Sequence =>
            // assert (node_depth(tree,left) > 0);
            var (leftVars, leftResult) := MDTraversal(tree, left, curVars);
            if leftResult.Valid? then
              var (rightVars, rightResult) := MDTraversal(tree, right, leftVars);
              assert rightResult.Valid? ==> forall x :: x in writeVars_task_nodes(node) ==>  x in rightVars;
              (rightVars, rightResult)
            else
              (leftVars, leftResult)
          //Left tree represents the default
          case Exclusive =>
            MDTraversal(tree, left,curVars)

          case Parallel =>
            var (leftVars, leftResult) := MDTraversal(tree, left, curVars);
            var (rightVars, rightResult) := MDTraversal(tree, right, curVars);

            if leftResult.Valid? && rightResult.Valid? then
              (leftVars + rightVars, MDValidationResult.Valid)
            else if !leftResult.Valid? then
              (leftVars, leftResult)
            else
              (rightVars, rightResult)

          case Loop =>
            var (bodyVars,bodyResult) := MDTraversal(tree, right,curVars);
            (bodyVars,bodyResult)
        }

      case ConditionNode() =>
        (curVars,MDValidationResult.Valid)

    }
  }





  datatype LDValidationResult =
      Valid
    | Invalid(node: Node, overwritten: set<string>)
  function CheckLostData(node: Node, unusedVars: set<string>, writeVars: set<string>): (result:(LDValidationResult, set<string>,set<string>))
    decreases node
    ensures result.0.Invalid? && node.TaskNode? ==> exists x :: x in result.1 && x in node.writeVariable
    ensures result.0.Valid? && node.TaskNode? ==> (unusedVars - node.readVariable) * node.writeVariable == {}

  {
    match node
    {
      case TaskNode(_, writeVariables, readVariables) =>

        var newUnusedVars := (unusedVars - readVariables);
        if writeVariables * newUnusedVars != {} then
          (LDValidationResult.Invalid(node,writeVariables * newUnusedVars),newUnusedVars,writeVars)

        else

          (LDValidationResult.Valid, newUnusedVars + writeVariables,writeVars+writeVariables)
      case OperatorNode(op, left, right) =>
        match op{
          case Sequence =>
            var (leftResult, leftUnusedVars,leftWrittenVars) := CheckLostData(left, unusedVars,writeVars);

            if leftResult.Invalid? then
              (leftResult, leftUnusedVars,leftWrittenVars)
            else

              var (rightResult, rightUnusedVars,rightWrittenVars) := CheckLostData(right, leftUnusedVars,leftWrittenVars);
              if rightResult.Invalid? then
                (rightResult, rightUnusedVars,rightWrittenVars)
              else
                (LDValidationResult.Valid, rightUnusedVars,rightWrittenVars)
          case Exclusive =>
            CheckLostData(left,unusedVars,writeVars)
          case Parallel =>
            var (leftResult, leftUnusedVars,leftWrittenVars) := CheckLostData(left, unusedVars,{});
            if leftResult.Invalid? then
              (leftResult, leftUnusedVars,{})
            else
              var (rightResult,rightUnusedVars,rightWrittenVars) := CheckLostData(right,unusedVars,{});
              if rightResult.Invalid? then
                (rightResult, rightUnusedVars,{})
              else (LDValidationResult.Valid, leftUnusedVars*rightUnusedVars+leftWrittenVars+rightWrittenVars,{})
          case _ =>
            (LDValidationResult.Valid,unusedVars,{})
        }

      case _ =>
        (LDValidationResult.Valid,unusedVars,{})

    }
  }

  // Check Redundant Data
  function CheckRD():()



  predicate ExistsInconsistentData(node: Node)
  {
    var IDCheckResult := CheckID(node);
    IDCheckResult.Valid?
  }


  lemma SequenceIDLemma1(node: Node)
    requires node.OperatorNode?
    requires node.op == Sequence
    requires ExistsInconsistentData(node.left) || ExistsInconsistentData(node.right)
    ensures ExistsInconsistentData(node)


  lemma SequenceIDLemma2(node: Node)
    requires node.OperatorNode?
    requires node.op == Sequence
    requires !ExistsInconsistentData(node.left) && !ExistsInconsistentData(node.right)
    ensures !ExistsInconsistentData(node)
  {}


  lemma ParallelIDLemma(node: Node)
    requires node.OperatorNode?
    requires node.op == Parallel
    requires ExistsInconsistentData(node.left) || ExistsInconsistentData(node.right)
    ensures !ExistsInconsistentData(node)


  lemma SequenceMDLemma(node: Node)
    requires node.OperatorNode?
    requires node.op == Sequence


  predicate IsMDInitialState(tree: Node, node: Node, curVars: set<string>)
    requires MPST(node) && MPST(tree)
    requires node_in_tree(tree,node)
  {
    node_depth(tree,node) == 0 ==> |curVars| == 0
  }

}
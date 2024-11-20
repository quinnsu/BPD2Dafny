include "./Common/Elements.dfy"
include "./Common/Properties.dfy"
include "./Examples/Manufacturing.dfy"
include "./Proof/Predicates.dfy"

module Check{
  import opened Basic_Elements
  import opened Properties
  import opened manufacturing_case
  import opened Predicates




method  Case1_MD()

{

    var case1 := MFGCaseConstructor();

    //MD Check
    var (resultVars, validationResult):= CheckMD(case1,{});
    assert (validationResult.Valid?);
    //编译部分 若出现MissingData 打印出第一个遇到的MissingVar
    if (validationResult.Invalid?)
    {
       // print "Missing Data:",validationResult.missingVar;
    }

}

method{:timeLimit 30} Case1_ID()
{

  var case1 := MFGCaseConstructor();

  assert (ExistsInconsistentData(case1));

}

method{:timeLimit 30} Case1_LD()
{
  var case1 := MFGCaseConstructor();
  var (CheckLDcase1Result,SET1,SET2) := CheckLostData(case1,{},{});
  assert (CheckLDcase1Result.Valid?);
}


function GetRightmostTask(node:Node): Node 
  decreases node
  {
    match node{
      case OperatorNode(op,_,right) =>
        GetRightmostTask(right)
        //这个地方应该还要对op进一步判断的，此处仅考虑只有sequence operator的情况
      case Empty =>
       //Empty表示子树已经没有task了en
        node
      case TaskNode(_,_,_) =>
        node
      case ConditionNode() =>
        node
    }
  }



  lemma SequenceLemma(node: Node)
  requires node.OperatorNode?
  requires node.op == Sequence
  ensures CheckLostData(node,{},{}).0.Valid? ==> CheckLostData(node.left,{},{}).0.Valid? && CheckLostData(node.right,{},{}).0.Valid?
  ensures CheckLostData(node,{},{}).0.Invalid? ==> CheckLostData(node.left,{},{}).0.Valid? || CheckLostData(node.right,{},{}).0.Valid?
  //predicate CheckURAnomalies(tasks: seq<Node>)
  
  //predicate CheckURAnomalies



}

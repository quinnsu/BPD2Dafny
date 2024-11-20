include "./Elements.dfy"
include "../Proof/Proofs.dfy"

module Properties{

import opened Basic_Elements
import opened Proofs

//Incosistent Data Check
//IDCheck的返回结果，Valid结果包括读变量集合，写变量集合；Invalid结果里会包括读写冲突和写写冲突
datatype IDValidationResult = Valid(writeVars: set<string>, readVars: set<string>) | Invalid( WRC: set<string>, WWC: set<string>)

//检查Inconsistent Data
//对于parallel node, 分别检查左子树的写变量是否和右子树的读/写变量有冲突，右子树的写变量是否和左子树的读/写变量有冲突
function CheckID(node: Node) : (result : IDValidationResult)
ensures node.TaskNode? ==> result.Valid?
ensures result.Invalid? ==> (result.WRC != {} || result.WWC != {})
decreases node
{
 match node
 {
  case OperatorNode (op,left,right) =>
    match op{
      //对于parallel节点 检查两个子树是否有ID，如果都没有，则要检查该节点是否冲突
      case Parallel =>   
        var leftResult := CheckID(left);
        if leftResult.Invalid? then
          leftResult
        else 
          var rightResult := CheckID(right);
          if rightResult.Invalid? then
           rightResult
          else 
          //两个子树都没有ID，检查该节点是否冲突
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
               
      //对于Sequence节点，检查两个子树是否有ID,如果都没有，则直接合并
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
      //XOR 默认左子树为default
      case Exclusive =>
          CheckID(left)
      //Loop 只要check 右子树循环体部分有没有冲突
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

//MissingDataCheck，即读的变量必须在之前写过
//中序遍历树的同时维护当前defined的序列,curVars记录了前序节点（不包括当前节点）写的所有写变量，若valid则继续遍历，若invalid则返回当前节点和不满足的读变量
//result.0 记录了加上当前节点的所有写变量（离开节点时更新）
//在operatorNode维护curVars，在task进行判断
//如何证明： 到当前的这个node curVars记录了所有在他之前（前序节点）的task的写变量

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
  ensures node.TaskNode? && result.1.Valid? ==> node.readVariable <= curVars //遍历到task，结果为valid，则该节点的读变量包含在当前defined的变量里
  ensures node.TaskNode? && result.1.Invalid? ==>  exists x :: x in node.readVariable && x !in curVars
  ensures node.TaskNode? ==> node.writeVariable <= result.0
  ensures IsMDInitialState(tree,node,curVars)
  // all the write variables of task nodes in a tree are updated as the result
  ensures MPST(node) && result.1.Valid? ==> forall x :: x in writeVars_task_nodes(node) ==>  x in result.0 

{
    match node 
    {
     
      //遍历到task node 加上新的defined variables
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
         //对于并行网关，同时遍历两个子树都有效则返回合并结果，无效则返回无效结果
         case Parallel =>
          var (leftVars, leftResult) := MDTraversal(tree, left, curVars);
          var (rightVars, rightResult) := MDTraversal(tree, right, curVars);
  
          if leftResult.Valid? && rightResult.Valid? then
          (leftVars + rightVars, MDValidationResult.Valid)
          else if !leftResult.Valid? then
          (leftVars, leftResult)
          else
          (rightVars, rightResult)
          //只要有loop,就要避免右子树有MD 
          case Loop =>
            var (bodyVars,bodyResult) := MDTraversal(tree, right,curVars);
            (bodyVars,bodyResult)
            }
       
       case ConditionNode() =>
           (curVars,MDValidationResult.Valid)
       
    }
  }




    // 检查Lost Data
  //Lost Data: 定义(write)了一个变量，后面的任务还没有使用(read)，就再次write了
  //遍历的过程中维护当前defined且没用used的序列,如果遇到write一个新变量，就把该变量加到unused里，如果遇到read一个变量且变量在unused里，则把他删去
  //Strong的话就是xor的两条路都查看
  // result 里 第一个参数是特定类型的result，第二个参数是当前的新的unused的变量，第三个参数是给parallel情况用的新写入的变量
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
      //unsed - read 如果前面的unsed变量里和write变量有交集，则直接返回invalid结果，并且返回该overwritten的变量
        var newUnusedVars := (unusedVars - readVariables);
        if writeVariables * newUnusedVars != {} then
          (LDValidationResult.Invalid(node,writeVariables * newUnusedVars),newUnusedVars,writeVars)
        //没有交集的话应该要把这个read和write的信息记录下来吧
        else
           // 更新未使用变量集合
          (LDValidationResult.Valid, newUnusedVars + writeVariables,writeVars+writeVariables)
      case OperatorNode(op, left, right) =>
        match op{
          case Sequence =>
            var (leftResult, leftUnusedVars,leftWrittenVars) := CheckLostData(left, unusedVars,writeVars);
            // 检查左子树结果
            if leftResult.Invalid? then
              (leftResult, leftUnusedVars,leftWrittenVars)
            else
              // 检查右子树结果
              var (rightResult, rightUnusedVars,rightWrittenVars) := CheckLostData(right, leftUnusedVars,leftWrittenVars);
              if rightResult.Invalid? then
                (rightResult, rightUnusedVars,rightWrittenVars)
              else
                (LDValidationResult.Valid, rightUnusedVars,rightWrittenVars) // 如果两个子树都有效，返回有效和更新的未使用变量,writtenVars的逻辑和unsed相同
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


// 对于SeqNode 左子树或者右子树有ID 就会导致有ID
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
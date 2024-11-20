include "../Common/Elements.dfy"
module Proofs{
    import opened Basic_Elements

/**
  Count the size of a tree, including those lazy-deleted nodes(temporarylly marked as
  `deleted` and still exist in tree `t` until the next whole rebuilt)
*/
function size(t: Node): (s: nat)
{
  match t
  case TaskNode(_,_,_) => 1
  case OperatorNode(_,l,r) => size(l) + size(r)
  case ConditionNode() => 0
}

/**
  Recursive definition of MPST
*/
predicate MPST(t: Node)
{
    match t
    case TaskNode(_,_,_) => true
    case ConditionNode() => false
    case OperatorNode(op,l,r) =>
        match op 
            case Loop => l.ConditionNode? && MPST(r)
            case _ => MPST(l) && MPST(r)
       
}

lemma MPSTTransmission(t: Node)
requires MPST(t) && t.OperatorNode?
ensures MPST(t.left) && MPST(t.right)

/**
  Collect all nodes in a tree
*/
function tree_nodes(t: Node): (s: set<Node>)
 requires MPST(t)
 ensures MPST(t) ==> forall n :: n in s ==> MPST(n)
{
  match t
  case OperatorNode(_, l, r) =>
   MPSTTransmission(t);
   tree_nodes(l) + {t} + tree_nodes(r)
  case _ => {t}
}



/**
  Collect all task nodes in a tree
*/

function task_nodes(t: Node):(s:set<Node>)
    requires MPST(t) 
    ensures MPST(t) ==> forall n :: n in s ==> MPST(n)
    ensures MPST(t) ==> forall n :: n in s ==> n.TaskNode?
    ensures t.OperatorNode? ==> t !in s
    ensures  ConditionNode() !in s 
    {
        match t
            case TaskNode(_,_,_) => 
                {t}
            case OperatorNode(_,l,r) =>  
                MPSTTransmission(t);           
                task_nodes(l) + task_nodes(r)
            case _ => 
                {}
    }

/**
  Collect all write variables of task nodes in a tree
*/  


function writeVars_task_nodes(t: Node):(s:set<string>)
ensures t.TaskNode? ==> forall n :: n in t.writeVariable  <==> n in s
ensures t.OperatorNode? && ( t.op == Exclusive) ==> (forall n :: n in s <==>  n in writeVars_task_nodes(t.left) )
ensures t.OperatorNode? && (t.op == Parallel || t.op == Sequence) ==> (forall n :: n in s <==> n in writeVars_task_nodes(t.left) || n in writeVars_task_nodes(t.right))
ensures t.OperatorNode? && (t.op == Loop) ==> (forall n :: n in s <==> n in writeVars_task_nodes(t.right))
{
     match t
        case TaskNode(_,_,_) => 
            t.writeVariable
        case OperatorNode(op,l,r) =>
            match op{
                case Sequence =>
                    writeVars_task_nodes(l) + writeVars_task_nodes(r)
                case Exclusive =>
                    writeVars_task_nodes(l)
                case Loop =>
                    writeVars_task_nodes(r)
                case Parallel =>
                    writeVars_task_nodes(l) + writeVars_task_nodes(r)
            }
        case _=>
            {}
}


/**
    Collect all predecessor task nodes and the current node of a tree

 function pre_task_nodes(t: Node):(s:set<Node>)
 ensures MPST(t) ==> forall n :: n in s ==> MPST(n)
 ensures MPST(t) ==> forall n :: n in s ==> n.TaskNode?
 ensures t.OperatorNode? ==> t !in s
 ensures  ConditionNode() !in s 
 ensures t.OperatorNode? && (t.op == Sequence || (t.op == Exclusive)) ==> (forall n :: n in s <==> n in pre_task_nodes(t.left))
 ensures t.OperatorNode? && (t.op == Parallel) ==> (forall n :: n in s <==> n in pre_task_nodes(t.left) || n in pre_task_nodes(t.right))
 ensures t.OperatorNode? && (t.op == Loop) ==> (forall n :: n in s <==> n in pre_task_nodes(t.right))
 {
    match t
        case TaskNode(_,_,_) => 
            {t}
        case OperatorNode(op,l,r) =>
            match op{
                case Sequence =>
                    pre_task_nodes(l)
                case Exclusive =>
                    pre_task_nodes(l)
                case Loop =>
                    pre_task_nodes(r)
                case Parallel =>
                    pre_task_nodes(l) + pre_task_nodes(r)
            }
        case _=>
            {}
 }
  */
 
 /** 
    Collect all write variables of current task node and predecessor task nodes of a tree
    */
function writeVars_pre_task_nodes(t: Node):(s:set<string>)
ensures t.TaskNode? ==> forall n :: n in t.writeVariable  <==> n in s
ensures t.OperatorNode? && (t.op == Sequence || (t.op == Exclusive)) ==> (forall n :: n in s <==>  n in writeVars_pre_task_nodes(t.left) )
ensures t.OperatorNode? && (t.op == Parallel) ==> (forall n :: n in s <==> n in writeVars_pre_task_nodes(t.left) || n in writeVars_pre_task_nodes(t.right))
ensures t.OperatorNode? && (t.op == Loop) ==> (forall n :: n in s <==> n in writeVars_pre_task_nodes(t.right))
{
     match t
        case TaskNode(_,_,_) => 
            t.writeVariable
        case OperatorNode(op,l,r) =>
            match op{
                case Sequence =>
                    writeVars_pre_task_nodes(l)
                case Exclusive =>
                    writeVars_pre_task_nodes(l)
                case Loop =>
                    writeVars_pre_task_nodes(r)
                case Parallel =>
                    writeVars_pre_task_nodes(l) + writeVars_pre_task_nodes(r)
            }
        case _=>
            {}
}

/**
  Calculate the (relative) depth of a node n in the tree t, starting from 0
*/
function node_depth(t: Node, n: Node):(d:nat)
requires  MPST(t) && node_in_tree(t,n) 
ensures d >= 0
{
    
    if n == t then 0
    else match t{
        case TaskNode => 1
        case ConditionNode => 1
        case OperatorNode(_,l,r) =>
            //NodeLemma2(t,n);
            //assert node_in_tree(t,n.left);
            var leftDepth := node_depth(l,n);
            var rightDepth := node_depth(r,n);
            //assert max(leftDepth,rightDepth) >= node_depth(t,n);
            //assert max(leftDepth,rightDepth) + 1 > node_depth(t,n);
            max(leftDepth,rightDepth) + 1

    }
}

/**
  Determine if a node n is in the tree t
*/
predicate node_in_tree(t: Node, n: Node)
requires MPST(t)
{
  n in tree_nodes(t)
}

/** 
the operator node's depth relatively to tree t should be smaller than
both of its left child and right child's depth relatively to tree t */
lemma NodeLemma( t: Node,n: Node)
requires MPST(t) && MPST(n) && n.OperatorNode? && node_in_tree(t,n) 
ensures  node_in_tree(t,n.left)
ensures node_depth(t,n) < node_depth(t,n.left)


/** 
if an operator node is in a tree t
both of its left child and right child are in the tree t */
lemma NodeLemma2( t: Node,n: Node)
requires MPST(t)&& n.OperatorNode? && node_in_tree(t,n)
ensures node_in_tree(t,n.left)
ensures node_in_tree(t,n.right)



/**
  Return the maximal value between two integer values x and y
*/
function max(x: int, y: int): (r: int)
  ensures r >= x && r >= y
  ensures x > y ==> r == x
  ensures y > x ==> r == y
  ensures x == y ==> r == x == y
{
  if x > y then x else y
}

}



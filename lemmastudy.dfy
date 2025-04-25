// lemma学习小例子，加油我一定能看懂
// count function用来计算序列里true值的个数
function count(a:seq<bool>):nat
{
  if |a| == 0 then 0
  else (if a[0] then 1 else 0) + count(a[1..])
}

method m2(a: seq<bool>, b:seq<bool>)
  requires |a| > 0
{
  assert count(a) == count([a[0]]) + count(a[1..]);

  assert count(a+b) == count(a) + count(b);
}

lemma DistributeLemma(a: seq<bool>,b:seq<bool>)
  ensures count(a+b) == count(a) + count(b)
{
  if a == []{
    assert a + b == b;
    assert count(a) == 0;
    assert count(a + b) == count(b);
    assert count(a + b) == count(a) + count(b);
  }
  else{
    assert a ==[a[0]] + a[1..];
    assert a  == [a[0]] + a[1..] ;
    assert count (a ) == count(a[1..]) + count([a[0]]);
    assert a + b == [a[0]] + (a[1..] + b);
    assert count(a + b) == count([a[0]]) + count(a[1..] + b);

  }
}


datatype LDValidationResult =
    Valid
  | Invalid(node: Node, overwritten: set<string>)
function CheckLostData(node: Node, unusedVars: set<string>, writtenVars: set<string>): (result:(LDValidationResult, set<string>, set<string>))
  decreases node
  ensures result.0.Invalid? && node.TaskNode? ==> result.1 * node.writeVariable != {}
  ensures result.0.Valid? && node.TaskNode? ==> (unusedVars - node.readVariable) * node.writeVariable == {}

{
  match node
  {
    case TaskNode(_, writeVariables, readVariables) =>

      if writeVariables * (unusedVars - readVariables) != {} then
        (LDValidationResult.Invalid(node,writeVariables * (unusedVars - readVariables)),unusedVars - readVariables, writtenVars)

      else

        var newUnusedVars := (unusedVars - readVariables) + writeVariables;
        (LDValidationResult.Valid, newUnusedVars, writtenVars)
    case OperatorNode(op, left, right) =>
      match op{
        case Sequence =>
          var (leftResult, leftUnusedVars,leftWrittenVars) := CheckLostData(left, unusedVars,writtenVars);

          if leftResult.Invalid? then
            (leftResult, leftUnusedVars,leftWrittenVars)
          else

            var (rightResult, rightUnusedVars,rightWrittenVars) := CheckLostData(right, leftUnusedVars,leftWrittenVars);
            if rightResult.Invalid? then
              (rightResult, rightUnusedVars,rightWrittenVars)
            else
              (LDValidationResult.Valid, rightUnusedVars,rightWrittenVars)
        case Parallel =>
          var (leftResult, leftUnusedVars,leftWrittenVars) := CheckLostData(left, unusedVars,{});
          var (rightResult, rightUnusedVars,rightWrittenVars) := CheckLostData(right, unusedVars,{});
          // 检查左子树结果
          if leftResult.Invalid? then
            (leftResult, leftUnusedVars,leftWrittenVars)
          else
          // 检查右子树结果
          if rightResult.Invalid? then
            (rightResult, rightUnusedVars,rightWrittenVars)
          else
            (LDValidationResult.Valid, rightUnusedVars * leftUnusedVars + leftWrittenVars + rightWrittenVars ,leftWrittenVars + rightWrittenVars ) // 如果两个子树都有效，返回有效和更新的未使用变量
        case Exclusive =>
          var (leftResult, leftUnusedVars, leftWrittenVars) := CheckLostData(left, unusedVars,writtenVars);
          if leftResult.Invalid? then
            (leftResult, leftUnusedVars, leftWrittenVars)
          else
            (LDValidationResult.Valid, leftUnusedVars, leftWrittenVars)
        case _ =>
          (LDValidationResult.Valid, {},{})
      }

    case _ =>
      (LDValidationResult.Valid, {},{})

  }
}


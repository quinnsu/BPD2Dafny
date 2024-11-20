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
  //这个分配律人脑想想很显然，但证不出来, 但加了lemma就能整出来了
  DistributeLemma(a,b);
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
      //unsed - read 如果前面的unsed变量里和write变量有交集，则直接返回invalid结果，并且返回该overwritten的变量
        if writeVariables * (unusedVars - readVariables) != {} then
          (LDValidationResult.Invalid(node,writeVariables * (unusedVars - readVariables)),unusedVars - readVariables, writtenVars)
        //没有交集的话应该要把这个read和write的信息记录下来吧
        else
           // 更新未使用变量集合
          var newUnusedVars := (unusedVars - readVariables) + writeVariables;
          (LDValidationResult.Valid, newUnusedVars, writtenVars)
      case OperatorNode(op, left, right) =>
        match op{
          case Sequence =>
            var (leftResult, leftUnusedVars,leftWrittenVars) := CheckLostData(left, unusedVars,writtenVars);
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
          case Parallel =>
            var (leftResult, leftUnusedVars,leftWrittenVars) := CheckLostData(left, unusedVars,{}); //这里遇到parallel就把入口处writtenVars置空
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


   var seq1 := OperatorNode(
        Sequence,  // 左侧子树是顺序执行
        TaskNode(
            "Process_Breakdown",  // 处理分解
            {"Cost Data"},                    // 写入变量
            {"Process Parameters"} // 读取变量
        ),
        OperatorNode(
            Sequence, // 继续顺序执行
            TaskNode(
            "Shop_Floor_Segmentation", // 车间分割
            {},                // 写入变量
            {"MRP","Production Capacity"} // 读取变量
            ),
             TaskNode(
            "Route_Synthesis", // 路由合成
            {"BOM", "Key Materials"}, // 写入变量
            {}                      // 读取变量
            )
        )  
    );

    var seq2 := OperatorNode(
      Sequence,  // 右侧子树是顺序执行
      TaskNode(
            "Schedule_Adjustment", // 调度调整
            {"Process Parameters", "Cost Data"}, // 写入变量
            {}                      // 读取变量
          ),
      
      TaskNode(
      "Stock_Alert", // 库存警报
      {},             // 写入变量
      {}              // 读取变量
      )
    );
    //loop1: 左半张图
    var loop1 := OperatorNode(
      Sequence,
      seq1,
      OperatorNode(
        Loop,
        ConditionNode(),
        OperatorNode(
          Sequence,
          seq2,
          seq1
        )
      )
    );

    var par1 := OperatorNode(
      Parallel, // 顶层是并行网关
      OperatorNode(
          Sequence, // 左侧子树
          TaskNode(
              "Rough Scheduling", // 左侧的工作日历
              {"Part Requirement","Work Calendar"},  // 写入变量
              {"Work Calendar", "Key Materials"} // 读取变量
          ),
          OperatorNode(
              Sequence, // 嵌套的顺序操作
              TaskNode(
                  "Fine Scheduling",  // 左侧的精细调度
                  {"Part Order"},    // 写入变量
                  {"Work Calendar", "Key Materials","Lead Time"} // 读取变量
              ),
              TaskNode(
                  "Actual Production", // 左侧的实际生产
                  {},                  // 写入变量
                  {}                   // 读取变量
              )        
          )
      ),
      OperatorNode(
          Sequence, // 右侧子树
          TaskNode(
              "Work Calendar", // 右侧的工作日历
              {},              // 写入变量
              {"Work Calendar (read)", "Key Materials (read)"} // 读取变量
          ),
          OperatorNode(
          Sequence, // 右侧子树
          TaskNode(
              "Rough Scheduling", // 右侧的工作日历
              {},  // 写入变量
              {} // 读取变量
          ),
          OperatorNode(
              Sequence, // 嵌套的顺序操作
              TaskNode(
                  "Fine Scheduling",  
                  {},    // 写入变量
                  {} // 读取变量
              ),
              TaskNode(
                  "Actual Production", 
                  {},                  // 写入变量
                  {}                   // 读取变量
              )        
          )
      )
      )
);

    var loop2 := OperatorNode(
      Sequence,
      TaskNode(
        "Exception Management",
        {"Order Status","Exception Types"},
        {}
      ),
      OperatorNode(
        Loop,
        ConditionNode(),
        TaskNode(
        "Exception Management",
        {"Order Status","Exception Types"},
        {}
      )
      )
    );

    var seq3 := OperatorNode(
      Sequence,
      OperatorNode(
        Sequence, // 顺序操作
        TaskNode(
            "Ability Match", // 第一个任务
            {"Lead Time"},   // 写入变量
            {"Part Requirement "} // 读取变量
        ),
        TaskNode(
            "Order Matching", // 第二个任务
            {"Lead Time"},   // 写入变量
            {"Part Order"} // 读取变量
        )),
      OperatorNode(
        Sequence,
        loop2,
        TaskNode(
          "Order Confirmation",
          {},
          {}
        ))
    );
    //par2: 右半张图
    var par2 := OperatorNode(
      Parallel,
      par1,
      seq3
    );
    var case1 := OperatorNode(
      Sequence,
      loop1,
      par2
    );







function CheckMD(node: Node, curVars: set<string>) : (result: (set<string>, MDValidationResult))
  decreases node
  ensures node.TaskNode? && result.1.Valid? ==> node.readVariable <= curVars //遍历到task，结果为valid，则该节点的读变量包含在当前defined的变量里
  ensures node.TaskNode? && result.1.Invalid? ==>  exists x :: x in node.readVariable && x !in curVars
  ensures MPST(node) ==> forall x :: x in writeVars_pre_task_nodes(node) ==>  x in curVars
  {
    match node 
    {
      case Empty => (curVars,MDValidationResult.Valid)
      //遍历到task node 加上新的defined variables
      case TaskNode(_,definedVariable,readVariable) =>
       if readVariable <= curVars then
        (curVars + definedVariable, MDValidationResult.Valid)
      else
        (curVars, MDValidationResult.Invalid(node, readVariable))
        
      //For the sake of brevity, only the sequence operator is considered.
      case OperatorNode(op,left,right) =>
       match op{
         case Sequence =>
           var (leftVars, leftResult) := CheckMD(left, curVars);
           if leftResult.Valid? then
              var (rightVars, rightResult) := CheckMD(right, leftVars);
              (rightVars, rightResult)
            else
            (leftVars, leftResult)
        //Left tree represents the default
         case Exclusive =>
          CheckMD(left,curVars)
         //对于并行网关，同时遍历两个子树都有效则返回合并结果，无效则返回无效结果
         case Parallel =>
          var (leftVars, leftResult) := CheckMD(left, curVars);
          var (rightVars, rightResult) := CheckMD(right, curVars);
  
          if leftResult.Valid? && rightResult.Valid? then
          (leftVars + rightVars, MDValidationResult.Valid)
          else if !leftResult.Valid? then
          (leftVars, leftResult)
          else
          (rightVars, rightResult)
          //只要有loop,就要避免右子树有MD 
          case Loop =>
            var (bodyVars,bodyResult) := CheckMD(right,curVars);
            (bodyVars,bodyResult)
            }
       
       case ConditionNode() =>
           (curVars,MDValidationResult.Valid)
       
    }
  }
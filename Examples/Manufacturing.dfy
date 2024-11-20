include "../Common/Elements.dfy"
module manufacturing_case
{
    import opened Basic_Elements

function MFGCaseConstructor():(n:Node)
//构造的制造业例子，包括24个bpmn元素，13个数据对象
{
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
    case1
}

}
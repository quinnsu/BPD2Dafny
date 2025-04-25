include "../Common/Elements.dfy"
module manufacturing_case
{
  import opened Basic_Elements

  function MFGCaseConstructor():(n:Node)
    //a manufacturing case
  {
    var seq1 := OperatorNode(
                  Sequence,
                  TaskNode(
                    "Process_Breakdown",
                    {"Cost Data"},
                    {"Process Parameters"}
                  ),
                  OperatorNode(
                    Sequence,
                    TaskNode(
                      "Shop_Floor_Segmentation", // shop floor segmentation
                      {},
                      {"MRP","Production Capacity"}
                    ),
                    TaskNode(
                      "Route_Synthesis",
                      {"BOM", "Key Materials"},
                      {}
                    )
                  )
                );

    var seq2 := OperatorNode(
                  Sequence,
                  TaskNode(
                    "Schedule_Adjustment",
                    {"Process Parameters", "Cost Data"},
                    {}
                  ),

                  TaskNode(
                    "Stock_Alert",
                    {},
                    {}
                  )
                );

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
                  Parallel,
                  OperatorNode(
                    Sequence,
                    TaskNode(
                      "Rough Scheduling",
                      {"Part Requirement","Work Calendar"},
                      {"Work Calendar", "Key Materials"}
                    ),
                    OperatorNode(
                      Sequence,
                      TaskNode(
                        "Fine Scheduling",
                        {"Part Order"},
                        {"Work Calendar", "Key Materials","Lead Time"}
                      ),
                      TaskNode(
                        "Actual Production",
                        {},
                        {}
                      )
                    )
                  ),
                  OperatorNode(
                    Sequence,
                    TaskNode(
                      "Work Calendar",
                      {},
                      {"Work Calendar (read)", "Key Materials (read)"}
                    ),
                    OperatorNode(
                      Sequence,
                      TaskNode(
                        "Rough Scheduling",
                        {},
                        {}
                      ),
                      OperatorNode(
                        Sequence, // 嵌套的顺序操作
                        TaskNode(
                          "Fine Scheduling",
                          {},
                          {}
                        ),
                        TaskNode(
                          "Actual Production",
                          {},
                          {}
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
                    Sequence,
                    TaskNode(
                      "Ability Match",
                      {"Lead Time"},
                      {"Part Requirement "}
                    ),
                    TaskNode(
                      "Order Matching",
                      {"Lead Time"},
                      {"Part Order"}
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
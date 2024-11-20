include "../Common/Elements.dfy"
include "../Common/Properties.dfy"
include "../Proof/Proofs.dfy"

module Components_Tests{
    import opened Basic_Elements
    import opened Properties
    import opened Proofs

   


    function SeqCaseConstructor(): (Node, Node )
    // trivial example of sequence of 3 tasks
    {
        var s1 :=  OperatorNode(Sequence, TaskNode("Create_order",{"id","customer_name","order_items"},{}),
                OperatorNode(Sequence,TaskNode("Ship_order",{},{"id","customer_name"}),TaskNode("Record_order",{},{"id","customer_name"})));
        
        var s2 := OperatorNode(Sequence, TaskNode("Create_order",{},{}),
              OperatorNode(Sequence,TaskNode("Ship_order",{},{"id"}),TaskNode("Record_order",{},{"id"})));
        (s1,s2)
    }

    method SeqTest()
    {
        var(s1,s2) := SeqCaseConstructor();
        var validationResult:= CheckMD(s1);
        assert (validationResult == MDValidationResult.Valid);

        var validationResult2 := CheckMD(s2);
        assert (validationResult2 == MDValidationResult. Valid);

        // The second seq case occurs the Missing Data Error
    }

    function LoopCaseConstructor(): Node
    // parallel example with loop
    {
    var p1 := OperatorNode(
    Sequence,
    OperatorNode(
        Sequence,
        TaskNode(
        "receive_order",
        {"order_id", "customer_name", "order_items"},
        {}
        ),
        OperatorNode(
        Parallel,
        TaskNode(
            "prepare_materials",
            {"product_id"},
            {"order_id", "required_materials"}
        ),
        OperatorNode(
            Loop,
            ConditionNode(),
            TaskNode(
            "quality_check",
            {"customer_name"},
            {"order_id"}
            )
        // Loop的右子树可以是一个空节点或其他节点
        )
        )
    ),
        OperatorNode(
            Sequence,
            TaskNode(
            "assemble_product",
            {"product_id"},
            {"order_id"}
            ),
            TaskNode(
            "inspect_product",
            {"product_id"},
            {"order_id"}
            )
        )
    );
    p1
    }

    method LoopTest()
    {
        var p1 := LoopCaseConstructor();
        var IDCheckResult4 := CheckID(p1);
        assert (IDCheckResult4.Valid?);
        // No ID error in this case
    }

    function ParCaseConstructor():Node
    {
    var p2 := OperatorNode(
    Sequence,
    OperatorNode(
        Sequence,
        TaskNode(
        "receive_order",
        {"order_id","customer_name","order_items"},
        {}
        ),
        OperatorNode(
        Parallel,
        TaskNode(
            "prepare_materials",
            {"product_id"},
            {"order_id","required_matierials"}
        ), 
        OperatorNode(
            Sequence,
            TaskNode(
            "assemble_product",
            {"product_id"},
            {"order_id"}
            ),
            TaskNode(
            "inspect_product",
            {"product_id"},
            {"order_id"}
            )
        )
        )
    ),
    TaskNode(
        "package",
        {},
        {"product_id", "order_id"}
    )
    );
    p2}

    method ParTest1()
    {
        var p2 := ParCaseConstructor();
        assert(ExistsInconsistentData(p2));
        // p2 case occurs ID Error
    }
    method ParTest2()
    {
        var p2 := ParCaseConstructor();
        var validationResult := CheckMD(p2);
        assert (validationResult.Valid?);
        // p2 case occurs MD Error
    }

    method LDTest()
    {
      
      var par := OperatorNode(
      Parallel,
      TaskNode(
            "TASK1",  // 处理分解
            {"D1"},                    // 写入变量
            {""} // 读取变量
        ),
        TaskNode(
            "TASK2",  // 处理分解
            {"D1"},                    // 写入变量
            {} // 读取变量
        ));
        var seq3 := OperatorNode(
            Sequence,
            TaskNode(
            "TASK1",  // 处理分解
            {"D2"},                    // 写入变量
            {""} // 读取变量
        ),
        par
            );
        var (LDValidationResult,set1,set2):= CheckLostData(seq3,{},{});
        assert (LDValidationResult.Valid?);
        
        // Node_depth test 
        assert(node_depth(seq3,seq3) == 0 );
        assert(node_depth(seq3,par) == 1 );

    }

   
}
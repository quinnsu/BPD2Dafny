// Test to Run generated code


const engineModule = require('./engine.js');
try {
    const ProcessDefinitionModule = engineModule.ProcessDefinition;
    const OptionalModule = engineModule.Optional;
    const DafnyModule = engineModule._dafny;
    const BPMNStateModule = engineModule.BPMNState;
    const ExecutionInitModule = engineModule.ExecutionInit;
    const ExecutionEngineModule = engineModule.ExecutionEngine;
    const TokenModule = engineModule.Token;


    if (typeof ProcessDefinitionModule !== 'undefined' && typeof DafnyModule !== 'undefined') {
    
        
        // 1. 创建开始节点
        const startNode = ProcessDefinitionModule.Node.create_ProcessNode(
            DafnyModule.Seq.UnicodeFromString("start_1"),
            DafnyModule.Seq.UnicodeFromString("开始事件"),
            ProcessDefinitionModule.NodeType.create_StartEvent(),
            DafnyModule.Set.Empty,
            DafnyModule.Set.fromElements(DafnyModule.Seq.UnicodeFromString("flow_1")),
            OptionalModule.Option.create_None()
        );
        
        // 2. 创建任务数据配置（包含输入和输出变量）
        console.log("🔧 创建任务数据配置...");
        
        // 定义输入变量：customerName, orderAmount
        const inputVariables = DafnyModule.Seq.of(
            DafnyModule.Seq.UnicodeFromString("customerName"),
            DafnyModule.Seq.UnicodeFromString("orderAmount")
        );
        
        // 定义输出变量：processedOrder, approvalStatus
        const outputVariables = DafnyModule.Seq.of(
            DafnyModule.Seq.UnicodeFromString("processedOrder"),
            DafnyModule.Seq.UnicodeFromString("approvalStatus")
        );
        
        // 创建TaskData
        const taskData = ProcessDefinitionModule.TaskData.create_TaskDataConfig(
            inputVariables,
            outputVariables
        );
        
        console.log("✅ 任务数据配置创建成功");
        console.log(`   - 输入变量数量: ${taskData.dtor_inputVariables.length}`);
        console.log(`   - 输出变量数量: ${taskData.dtor_outputVariables.length}`);
        
        // 3. 创建带变量的用户任务节点
        const userTaskNode = ProcessDefinitionModule.Node.create_ProcessNode(
            DafnyModule.Seq.UnicodeFromString("task_1"),
            DafnyModule.Seq.UnicodeFromString("订单处理任务"),
            ProcessDefinitionModule.NodeType.create_Task(
                ProcessDefinitionModule.TaskType.create_UserTask(),
                OptionalModule.Option.create_Some(taskData)  // 包含变量配置
            ),
            DafnyModule.Set.fromElements(DafnyModule.Seq.UnicodeFromString("flow_1")),
            DafnyModule.Set.fromElements(DafnyModule.Seq.UnicodeFromString("flow_2")),
            OptionalModule.Option.create_None()
        );
        
        // 4. 创建结束节点
        const endNode = ProcessDefinitionModule.Node.create_ProcessNode(
            DafnyModule.Seq.UnicodeFromString("end_1"),
            DafnyModule.Seq.UnicodeFromString("结束事件"),
            ProcessDefinitionModule.NodeType.create_EndEvent(),
            DafnyModule.Set.fromElements(DafnyModule.Seq.UnicodeFromString("flow_2")),
            DafnyModule.Set.Empty,
            OptionalModule.Option.create_None()
        );
        
        // 5. 创建序列流
        const flow1 = ProcessDefinitionModule.SequenceFlow.create_Flow(
            DafnyModule.Seq.UnicodeFromString("flow_1"),
            DafnyModule.Seq.UnicodeFromString("start_1"),
            DafnyModule.Seq.UnicodeFromString("task_1"),
            OptionalModule.Option.create_None()
        );
        
        const flow2 = ProcessDefinitionModule.SequenceFlow.create_Flow(
            DafnyModule.Seq.UnicodeFromString("flow_2"),
            DafnyModule.Seq.UnicodeFromString("task_1"),
            DafnyModule.Seq.UnicodeFromString("end_1"),
            OptionalModule.Option.create_None()
        );
        
        // 6. 创建映射
        const nodes = new DafnyModule.Map();
        nodes.updateUnsafe(DafnyModule.Seq.UnicodeFromString("start_1"), startNode);
        nodes.updateUnsafe(DafnyModule.Seq.UnicodeFromString("task_1"), userTaskNode);
        nodes.updateUnsafe(DafnyModule.Seq.UnicodeFromString("end_1"), endNode);
        
        const flows = new DafnyModule.Map();
        flows.updateUnsafe(DafnyModule.Seq.UnicodeFromString("flow_1"), flow1);
        flows.updateUnsafe(DafnyModule.Seq.UnicodeFromString("flow_2"), flow2);
        
        // 7. 创建流程定义
        const processDef = ProcessDefinitionModule.ProcessDef.create_ProcessDefinition(
            DafnyModule.Seq.UnicodeFromString("simple_process"),
            DafnyModule.Seq.UnicodeFromString("简单测试流程"),
            nodes,
            flows,
            DafnyModule.Set.fromElements(DafnyModule.Seq.UnicodeFromString("start_1")),
            DafnyModule.Set.fromElements(DafnyModule.Seq.UnicodeFromString("end_1"))
        );
        
        console.log("✅ 流程定义创建成功");
        console.log(`📊 节点数: ${processDef.dtor_nodes.length}, 流数: ${processDef.dtor_flows.length}`);
        
        // 8. 验证流程定义
        console.log("\n🔍 验证流程定义...");
        const isValidProcess = BPMNStateModule.__default.ValidProcessDefinition(processDef);
        console.log(`   - 流程定义有效性: ${isValidProcess}`);
        
        if (isValidProcess) {
            // 9. 创建初始变量
            console.log("\n🎬 设置初始变量...");
            const VariablesModule = engineModule.Variables;
            const BigNumber = require('bignumber.js');
            let globalVariables = VariablesModule.__default.EmptyVariables();
            
            // 设置输入变量的初始值
            globalVariables = VariablesModule.__default.SetVariable(
                globalVariables,
                DafnyModule.Seq.UnicodeFromString("customerName"),
                VariablesModule.VariableValue.create_StringValue(DafnyModule.Seq.UnicodeFromString("张三"))
            );
            
            globalVariables = VariablesModule.__default.SetVariable(
                globalVariables,
                DafnyModule.Seq.UnicodeFromString("orderAmount"),
                VariablesModule.VariableValue.create_IntValue(new BigNumber(1000))
            );
            
            console.log("✅ 初始变量设置完成");
            console.log("   - customerName: 张三");
            console.log("   - orderAmount: 1000");
            
            // 10. 初始化执行状态
            console.log("\n🏁 初始化执行状态...");
            const runningState = ExecutionInitModule.__default.InitializeExecution(processDef);
            
            console.log("✅ 基本执行状态初始化成功");
            console.log(`   - 状态类型: ${runningState.is_Running ? 'Running' : runningState.toString()}`);
            
            // 11. 手动设置全局变量到运行状态
            console.log("\n🔧 设置运行状态的全局变量...");
            const process = runningState.dtor_process;
            const updatedProcess = BPMNStateModule.ProcessObj.create_Process(
                process.dtor_processId,
                process.dtor_tokenCollection,
                globalVariables,  // 使用我们设置的全局变量
                process.dtor_processDefinition,
                process.dtor_executionHistory,
                process.dtor_context
            );
            const initialState = BPMNStateModule.State.create_Running(updatedProcess);
            
            console.log("✅ 流程启动成功");
            console.log(`   - 状态类型: ${initialState.is_Running ? 'Running' : initialState.toString()}`);
            
            if (initialState.is_Running) {
                const process = initialState.dtor_process;
                const activeTokens = TokenModule.__default.GetActiveTokens(process.dtor_tokenCollection);
                console.log(`   - 活跃Token数量: ${activeTokens.length}`);
                
                // 执行步骤
                console.log("\n⚡ 开始执行流程步骤...");
                let currentState = initialState;
                let step = 1;
                const maxSteps = 5;
                
                while (step <= maxSteps && currentState.is_Running) {
                    console.log(`\n--- 步骤 ${step} ---`);
                    
                    const process = currentState.dtor_process;
                    const activeTokens = TokenModule.__default.GetActiveTokens(process.dtor_tokenCollection);
                    
                    if (activeTokens.length === 0) {
                        console.log("❌ 没有活跃的token，执行结束");
                        break;
                    }
                    
                    // 显示当前状态
                    const tokenId = activeTokens[0];
                    const token = process.dtor_tokenCollection.dtor_tokens.get(tokenId);
                    const currentNode = process.dtor_processDefinition.dtor_nodes.get(token.dtor_location);
                    
                    console.log(`🎯 当前Token位置: ${token.dtor_location}`);
                    console.log(`📝 当前节点名称: ${currentNode.dtor_name}`);
                    console.log(`🔧 节点类型: ${currentNode.dtor_nodeType.toString()}`);
                    
                    // 如果是任务节点，显示变量访问信息
                    if (currentNode.dtor_nodeType.is_Task) {
                        console.log("📋 检查任务变量访问:");
                        try {
                            const variableAccess = ExecutionEngineModule.__default.GetTokenVariableAccess(currentState, tokenId);
                            console.log(`   - 变量访问数量: ${variableAccess.length}`);
                            
                            // 显示每个变量访问
                            for (let i = 0; i < variableAccess.length; i++) {
                                const access = variableAccess[i];
                                const varName = access.dtor_variable.toString();
                                const accessType = access.dtor_accessType.is_Read ? "读取" : "写入";
                                console.log(`   - ${accessType} 变量: ${varName}`);
                            }
                        } catch (e) {
                            console.log("   - 获取变量访问信息出错:", e.message);
                        }
                    }
                    
                    // 执行一步
                    const nextState = ExecutionEngineModule.__default.ExecuteStep(currentState);
                    
                    // 检查执行结果
                    if (nextState.is_Running) {
                        console.log("✅ 执行成功，继续运行");
                        currentState = nextState;
                        
                        // 显示新状态
                        const newProcess = nextState.dtor_process;
                        const newActiveTokens = TokenModule.__default.GetActiveTokens(newProcess.dtor_tokenCollection);
                        
                        if (newActiveTokens.length > 0) {
                            const newTokenId = newActiveTokens[0];
                            const newToken = newProcess.dtor_tokenCollection.dtor_tokens.get(newTokenId);
                            console.log(`➡️  Token移动到: ${newToken.dtor_location}`);
                        }
                    } else if (nextState.is_Completed) {
                        console.log("🎉 流程执行完成!");
                        break;
                    } else if (nextState.is_Terminated) {
                        console.log("🛑 流程被终止");
                        break;
                    } else if (nextState.is_Error) {
                        console.log("❌ 执行出错:");
                        const errorCode = nextState.dtor_errorCode;
                        console.log(`   错误信息: ${errorCode.toString()}`);
                        break;
                    }
                    
                    step++;
                }
                
                if (step > maxSteps) {
                    console.log("⚠️  达到最大执行步数限制");
                }
                
                console.log("\n🏆 BPMN执行引擎测试完成!");
            } else {
                console.log("❌ 初始化状态不是Running状态");
            }
        } else {
            console.log("❌ 流程定义验证失败");
        }
    } else {
        console.log("❌ 关键模块未成功加载");
    }
    
} catch (error) {
    console.error("💥 测试过程中发生错误:", error);
    console.error("错误堆栈:", error.stack);
}

console.log("\n📄 测试完成。"); 
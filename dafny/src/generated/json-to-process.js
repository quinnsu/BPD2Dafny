
const fs = require('fs');
const path = require('path');

function convertJsonToProcessDefinition(jsonFilePath) {
    
    const jsonContent = fs.readFileSync(jsonFilePath, 'utf8');
    const model = JSON.parse(jsonContent);
    
    console.log(`process name: ${model.main_process.name}`);
    console.log(`total elements: ${model.statistics.total_elements}`);
    
    const elements = model.elements;
    const flows = model.flow;
    
    const startEvents = [];
    const endEvents = [];
    const tasks = [];
    const gateways = [];
    const sequenceFlows = [];
    
    const incomingFlows = {}; // nodeId -> [flowId, ...]
    const outgoingFlows = {}; // nodeId -> [flowId, ...]
    
    for (const elementId in elements) {
        incomingFlows[elementId] = [];
        outgoingFlows[elementId] = [];
    }
    
    for (const sourceId in flows) {
        const connections = flows[sourceId];
        for (const connection of connections) {
            const flowId = connection.sequence_id;
            const targetId = connection.target;
            
            sequenceFlows.push({
                id: flowId,
                name: connection.name || "",
                source: sourceId,
                target: targetId,
                condition: connection.condition
            });
            
            outgoingFlows[sourceId].push(flowId);
            incomingFlows[targetId].push(flowId);
        }
    }
    
    for (const elementId in elements) {
        const element = elements[elementId];
        element._id = elementId;
        
        switch (element.class) {
            case 'StartEvent':
                startEvents.push(element);
                break;
            case 'EndEvent':
                endEvents.push(element);
                break;
            case 'Task':
                tasks.push(element);
                break;
            case 'ParallelGateway':
            case 'ExclusiveGateway':
            case 'InclusiveGateway':
            case 'EventBasedGateway':
                gateways.push(element);
                break;
        }
    }
    
    console.log(`element classification statistics:`);
    console.log(`   - start event: ${startEvents.length}`);
    console.log(`   - end event: ${endEvents.length}`);
    console.log(`   - task: ${tasks.length}`);
    console.log(`   - gateway: ${gateways.length}`);
    console.log(`   - sequence flow: ${sequenceFlows.length}`);
    
    
    let code = generateProcessDefinitionCode(
        model.main_process,
        startEvents,
        endEvents, 
        tasks,
        gateways,
        sequenceFlows,
        incomingFlows,
        outgoingFlows
    );
    
    return code;
}

function generateProcessDefinitionCode(mainProcess, startEvents, endEvents, tasks, gateways, sequenceFlows, incomingFlows, outgoingFlows) {
    let code = `// Auto-generated BPMN Process Definition\n`;
    code += `// Source Process: ${mainProcess.name} (${mainProcess.id})\n`;
    code += `// Generated Time: ${new Date().toLocaleString()}\n\n`;
    
    code += `console.log("Starting execution of auto-generated BPMN process test...");\n\n`;
    
    code += `const engineModule = require('../engine.js');\n\n`;
    code += `try {\n`;
    code += `    const ProcessDefinitionModule = engineModule.ProcessDefinition;\n`;
    code += `    const OptionalModule = engineModule.Optional;\n`;
    code += `    const DafnyModule = engineModule._dafny;\n`;
    code += `    const BPMNStateModule = engineModule.BPMNState;\n`;
    code += `    const ExecutionInitModule = engineModule.ExecutionInit;\n`;
    code += `    const ExecutionEngineModule = engineModule.ExecutionEngine;\n`;
    code += `    const TokenModule = engineModule.Token;\n\n`;
    
    code += `    if (typeof ProcessDefinitionModule !== 'undefined' && typeof DafnyModule !== 'undefined') {\n`;
    code += `        console.log("Module imported successfully, starting to create process definition...");\n\n`;
    
    code += `        // === Create Process Nodes ===\n`;
    
    for (const startEvent of startEvents) {
        code += generateNodeCode(startEvent, 'StartEvent', incomingFlows, outgoingFlows);
    }
    
    for (const task of tasks) {
        code += generateNodeCode(task, 'Task', incomingFlows, outgoingFlows);
    }
    
    for (const gateway of gateways) {
        code += generateNodeCode(gateway, gateway.class, incomingFlows, outgoingFlows);
    }
    
    for (const endEvent of endEvents) {
        code += generateNodeCode(endEvent, 'EndEvent', incomingFlows, outgoingFlows);
    }
    
    code += `\n        // === Create Sequence Flows ===\n`;
    for (const flow of sequenceFlows) {
        code += generateSequenceFlowCode(flow);
    }
    
    code += generateMappingCode(startEvents, endEvents, tasks, gateways, sequenceFlows);
    code += generateProcessDefCode(mainProcess, startEvents, endEvents);
    code += generateExecutionCode();
    code += `    } else {\n`;
    code += `        console.error("module import failed");\n`;
    code += `    }\n`;
    code += `} catch (error) {\n`;
    code += `    console.error("error during execution:", error.message);\n`;
    code += `    console.error(error.stack);\n`;
    code += `}\n`;
    
    return code;
}

function generateNodeCode(element, nodeType, incomingFlows, outgoingFlows) {
    const nodeId = element._id;

    const rawName = element.name || "";
    const nodeName = rawName
        .replace(/\\/g, '\\\\')         
        .replace(/"/g, '\\"')           
        .replace(/\r?\n/g, " ")         
        .replace(/\r/g, " ")            
        .replace(/\t/g, " ")            
        .replace(/\s+/g, " ")           
        .trim();                        
    
    if (rawName !== nodeName) {
        console.log(`   string cleaning: "${rawName}" -> "${nodeName}"`);
    }
    
    const varName = `node_${nodeId.replace(/-/g, '_')}`;
    
    let code = `        // ${nodeType}: ${nodeName}\n`;
    code += `        const ${varName} = ProcessDefinitionModule.Node.create_ProcessNode(\n`;
    code += `            DafnyModule.Seq.UnicodeFromString("${nodeId}"),\n`;
    code += `            DafnyModule.Seq.UnicodeFromString("${nodeName}"),\n`;
    
    switch (nodeType) {
        case 'StartEvent':
            code += `            ProcessDefinitionModule.NodeType.create_StartEvent(),\n`;
            break;
        case 'EndEvent':
            code += `            ProcessDefinitionModule.NodeType.create_EndEvent(),\n`;
            break;
        case 'Task':
            code += `            ProcessDefinitionModule.NodeType.create_Task(\n`;
            code += `                ProcessDefinitionModule.TaskType.create_UserTask(),\n`;
            code += `                OptionalModule.Option.create_None()  // 空的任务数据配置\n`;
            code += `            ),\n`;
            break;
        case 'ParallelGateway':
            code += `            ProcessDefinitionModule.NodeType.create_Gateway(\n`;
            code += `                ProcessDefinitionModule.GatewayType.create_ParallelGateway()\n`;
            code += `            ),\n`;
            break;
        case 'ExclusiveGateway':
            code += `            ProcessDefinitionModule.NodeType.create_Gateway(\n`;
            code += `                ProcessDefinitionModule.GatewayType.create_ExclusiveGateway()\n`;
            code += `            ),\n`;
            break;
        case 'InclusiveGateway':
            code += `            ProcessDefinitionModule.NodeType.create_Gateway(\n`;
            code += `                ProcessDefinitionModule.GatewayType.create_InclusiveGateway()\n`;
            code += `            ),\n`;
            break;
        case 'EventBasedGateway':
            code += `            ProcessDefinitionModule.NodeType.create_Gateway(\n`;
            code += `                ProcessDefinitionModule.GatewayType.create_EventBasedGateway()\n`;
            code += `            ),\n`;
            break;
    }
    
    const incoming = incomingFlows[nodeId] || [];
    if (incoming.length > 0) {
        const flowRefs = incoming.map(flowId => `DafnyModule.Seq.UnicodeFromString("${flowId}")`).join(', ');
        code += `            DafnyModule.Set.fromElements(${flowRefs}),\n`;
    } else {
        code += `            DafnyModule.Set.Empty,\n`;
    }
    
    const outgoing = outgoingFlows[nodeId] || [];
    if (outgoing.length > 0) {
        const flowRefs = outgoing.map(flowId => `DafnyModule.Seq.UnicodeFromString("${flowId}")`).join(', ');
        code += `            DafnyModule.Set.fromElements(${flowRefs}),\n`;
    } else {
        code += `            DafnyModule.Set.Empty,\n`;
    }
    
    let defaultFlowCode = `            OptionalModule.Option.create_None()`;
    
    if (nodeType === 'ExclusiveGateway' && 
        (!element.default || element.default === null) && 
        outgoingFlows[nodeId] && outgoingFlows[nodeId].length > 0) {
        
        const firstOutgoingFlow = outgoingFlows[nodeId][0];
        defaultFlowCode = `            OptionalModule.Option.create_Some(DafnyModule.Seq.UnicodeFromString("${firstOutgoingFlow}"))`;
        
        console.log(`   default flow: ${nodeName || nodeId} -> ${firstOutgoingFlow}`);
    }
    
    code += defaultFlowCode + `\n`;
    code += `        );\n\n`;
    
    return code;
}

function generateSequenceFlowCode(flow) {
    const varName = `flow_${flow.id.replace(/-/g, '_')}`;
    
    let code = `        // sequence flow: ${flow.name}\n`;
    code += `        const ${varName} = ProcessDefinitionModule.SequenceFlow.create_Flow(\n`;
    code += `            DafnyModule.Seq.UnicodeFromString("${flow.id}"),\n`;
    code += `            DafnyModule.Seq.UnicodeFromString("${flow.source}"),\n`;
    code += `            DafnyModule.Seq.UnicodeFromString("${flow.target}"),\n`;
    code += `            OptionalModule.Option.create_None()  \n`;
    code += `        );\n\n`;
    
    return code;
}

function generateMappingCode(startEvents, endEvents, tasks, gateways, sequenceFlows) {
    let code = `        // === create node and flow mapping ===\n`;
    code += `        const nodes = new DafnyModule.Map();\n`;
    
    for (const event of startEvents) {
        const varName = `node_${event._id.replace(/-/g, '_')}`;
        code += `        nodes.updateUnsafe(DafnyModule.Seq.UnicodeFromString("${event._id}"), ${varName});\n`;
    }
    
    for (const task of tasks) {
        const varName = `node_${task._id.replace(/-/g, '_')}`;
        code += `        nodes.updateUnsafe(DafnyModule.Seq.UnicodeFromString("${task._id}"), ${varName});\n`;
    }
    
    for (const gateway of gateways) {
        const varName = `node_${gateway._id.replace(/-/g, '_')}`;
        code += `        nodes.updateUnsafe(DafnyModule.Seq.UnicodeFromString("${gateway._id}"), ${varName});\n`;
    }
    
    for (const event of endEvents) {
        const varName = `node_${event._id.replace(/-/g, '_')}`;
        code += `        nodes.updateUnsafe(DafnyModule.Seq.UnicodeFromString("${event._id}"), ${varName});\n`;
    }
    
    code += `\n        const flows = new DafnyModule.Map();\n`;
    
    for (const flow of sequenceFlows) {
        const varName = `flow_${flow.id.replace(/-/g, '_')}`;
        code += `        flows.updateUnsafe(DafnyModule.Seq.UnicodeFromString("${flow.id}"), ${varName});\n`;
    }
    
    code += `\n`;
    return code;
}

function generateProcessDefCode(mainProcess, startEvents, endEvents) {
    let code = `        // === create process definition ===\n`;
    code += `        const processDef = ProcessDefinitionModule.ProcessDef.create_ProcessDefinition(\n`;
    code += `            DafnyModule.Seq.UnicodeFromString("${mainProcess.id}"),\n`;
    code += `            DafnyModule.Seq.UnicodeFromString("${mainProcess.name}"),\n`;
    code += `            nodes,\n`;
    code += `            flows,\n`;
    
    if (startEvents.length > 0) {
        const startNodeRefs = startEvents.map(event => `DafnyModule.Seq.UnicodeFromString("${event._id}")`).join(', ');
        code += `            DafnyModule.Set.fromElements(${startNodeRefs}),\n`;
    } else {
        code += `            DafnyModule.Set.Empty,\n`;
    }
    
    if (endEvents.length > 0) {
        const endNodeRefs = endEvents.map(event => `DafnyModule.Seq.UnicodeFromString("${event._id}")`).join(', ');
        code += `            DafnyModule.Set.fromElements(${endNodeRefs})\n`;
    } else {
        code += `            DafnyModule.Set.Empty\n`;
    }
    
    code += `        );\n\n`;
    return code;
}

function generateExecutionCode() {
    let code = `        // === validate and execute process ===\n`;
    code += `        console.log("process definition created successfully");\n`;
    code += `        console.log(\`node count: \${processDef.dtor_nodes.length}, flow count: \${processDef.dtor_flows.length}\`);\n\n`;
    
    code += `        // validate process definition\n`;
    code += `        console.log("validate process definition...");\n`;
    code += `        const isValidProcess = BPMNStateModule.__default.ValidProcessDefinition(processDef);\n`;
    code += `        console.log(\`   - process definition validity: \${isValidProcess}\`);\n\n`;
    
    code += `        if (isValidProcess) {\n`;
    code += `            console.log("initialize execution state...");\n`;
    code += `            const initialState = ExecutionInitModule.__default.InitializeExecution(processDef);\n`;
    code += `            console.log(\`execution state initialized: \${initialState.is_Running ? 'Running' : initialState.toString()}\`);\n\n`;
    
    code += `            if (initialState.is_Running) {\n`;
    code += `                const process = initialState.dtor_process;\n`;
    code += `                const activeTokens = TokenModule.__default.GetActiveTokens(process.dtor_tokenCollection);\n`;
    code += `                console.log(\`   - active token count: \${activeTokens.length}\`);\n\n`;
    
    code += `                console.log("execute process steps...");\n`;
    code += `                let currentState = initialState;\n`;
    code += `                let step = 1;\n`;
    code += `                const maxSteps = 100;\n\n`;
    
    code += `                while (step <= maxSteps && currentState.is_Running) {\n`;
    code += `                    console.log(\`\\n--- Step \${step} ---\`);\n`;
    code += `                    const process = currentState.dtor_process;\n`;
    code += `                    const activeTokens = TokenModule.__default.GetActiveTokens(process.dtor_tokenCollection);\n\n`;
    
    code += `                    if (activeTokens.length === 0) {\n`;
    code += `                        console.log(" no active token, execution ended");\n`;
    code += `                        break;\n`;
    code += `                    }\n\n`;
    
    code += `                    const tokenId = activeTokens[0];\n`;
    code += `                    const token = process.dtor_tokenCollection.dtor_tokens.get(tokenId);\n`;
    code += `                    const currentNode = process.dtor_processDefinition.dtor_nodes.get(token.dtor_location);\n\n`;
    
                        code += `                    const locationStr = token.dtor_location.toVerbatimString ? token.dtor_location.toVerbatimString(false) : String(token.dtor_location);\n`;
                    code += `                    console.log(\`current token location: \${locationStr}\`);\n`;
                        code += `                    const nodeNameStr = currentNode.dtor_name.toVerbatimString ? currentNode.dtor_name.toVerbatimString(false) : String(currentNode.dtor_name);\n`;
                    code += `                    console.log(\`current node name: \${nodeNameStr}\`);\n`;
    code += `                    console.log(\`current node type: \${currentNode.dtor_nodeType.toString()}\`);\n\n`;
    
    code += `                    // execute one step\n`;
    code += `                    const nextState = ExecutionEngineModule.__default.ExecuteStep(currentState);\n`;
    code += `                    \n`;
    code += `                    // display system state\n`;
    code += `                    if (nextState.is_NotStarted) {\n`;
    code += `                        console.log("🔄 System State: NotStarted");\n`;
    code += `                    } else if (nextState.is_Running) {\n`;
    code += `                        console.log("▶️  System State: Running");\n`;
    code += `                        console.log("step executed successfully");\n`;
    code += `                        currentState = nextState;\n`;
    code += `                    } else if (nextState.is_Completed) {\n`;
    code += `                        console.log("✅ System State: Completed");\n`;
    code += `                        console.log("process executed successfully");\n`;
    code += `                        break;\n`;
    code += `                    } else if (nextState.is_Terminated) {\n`;
    code += `                        console.log("⏹️  System State: Terminated");\n`;
    code += `                        console.log("process was terminated");\n`;
    code += `                        break;\n`;
    code += `                    } else if (nextState.is_Error) {\n`;
    code += `                        console.log("❌ System State: Error");\n`;
    code += `                        const errorCode = nextState.dtor_errorCode;\n`;
    code += `                        if (errorCode.is_ValidationError) {\n`;
    code += `                            console.log("   Error Type: ValidationError -", errorCode.dtor_message.toVerbatimString(false));\n`;
    code += `                        } else if (errorCode.is_RuntimeError) {\n`;
    code += `                            console.log("   Error Type: RuntimeError -", errorCode.dtor_message.toVerbatimString(false));\n`;
    code += `                        } else if (errorCode.is_TimeoutError) {\n`;
    code += `                            console.log("   Error Type: TimeoutError -", errorCode.dtor_message.toVerbatimString(false));\n`;
    code += `                        } else if (errorCode.is_ResourceError) {\n`;
    code += `                            console.log("   Error Type: ResourceError -", errorCode.dtor_message.toVerbatimString(false));\n`;
    code += `                        } else if (errorCode.is_DeadlockError) {\n`;
    code += `                            console.log("   Error Type: DeadlockError -", errorCode.dtor_details.toVerbatimString(false));\n`;
    code += `                        } else if (errorCode.is_ExecutionError) {\n`;
    code += `                            console.log("   Error Type: ExecutionError - Node:", errorCode.dtor_nodeId.toVerbatimString(false), "Message:", errorCode.dtor_message.toVerbatimString(false));\n`;
    code += `                        } else if (errorCode.is_FlowError) {\n`;
    code += `                            console.log("   Error Type: FlowError - Flow:", errorCode.dtor_flowId.toVerbatimString(false), "Message:", errorCode.dtor_message.toVerbatimString(false));\n`;
    code += `                        } else if (errorCode.is_TokenError) {\n`;
    code += `                            console.log("   Error Type: TokenError - Token:", errorCode.dtor_tokenId, "Message:", errorCode.dtor_message.toVerbatimString(false));\n`;
    code += `                        } else if (errorCode.is_DefinitionError) {\n`;
    code += `                            console.log("   Error Type: DefinitionError -", errorCode.dtor_message.toVerbatimString(false));\n`;
    code += `                        } else if (errorCode.is_DataConflictError) {\n`;
    code += `                            console.log("   Error Type: DataConflictError - Conflicts:", errorCode.dtor_conflicts.length);\n`;
    code += `                        } else {\n`;
    code += `                            console.log("   Error Type: Unknown");\n`;
    code += `                        }\n`;
    code += `                        break;\n`;
    code += `                    } else {\n`;
    code += `                        console.log("❓ System State: Unknown");\n`;
    code += `                        console.log(\`process execution error: \${nextState.toString()}\`);\n`;
    code += `                        break;\n`;
    code += `                    }\n\n`;
    
    code += `                    step++;\n`;
    code += `                }\n\n`;
    
    code += `                console.log("process execution ended");\n`;
    code += `            }\n`;
    code += `        } else {\n`;
    code += `            console.error("process definition validation failed");\n`;
    code += `        }\n`;
    
    return code;
}

function main() {
    const args = process.argv.slice(2);
    if (args.length === 0) {
        console.log("usage: node json-to-process.js <json file path>");
        console.log("example: node json-to-process.js tests/parsed_models_03.json");
        return;
    }
    
    const jsonFilePath = args[0];
    
    try {
        const generatedCode = convertJsonToProcessDefinition(jsonFilePath);
        
        const basename = path.basename(jsonFilePath, '.json');
        const testsDir = './tests';
        const outputFile = path.join(testsDir, `generated-${basename}.js`);
        
        if (!fs.existsSync(testsDir)) {
            fs.mkdirSync(testsDir, { recursive: true });
        }
        
        fs.writeFileSync(outputFile, generatedCode, 'utf8');
        
        console.log(`\nconversion completed`);
        console.log(`generated test file: ${outputFile}`);
        console.log(`run command: node ${outputFile}`);
        
    } catch (error) {
        console.error("conversion error:", error.message);
        console.error(error.stack);
    }
}

// if directly run this script
if (require.main === module) {
    main();
}

module.exports = { convertJsonToProcessDefinition }; 
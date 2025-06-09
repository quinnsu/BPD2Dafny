# BPMN 2.0 Execution Engine (Generated from Dafny)

This directory contains a JavaScript implementation of a BPMN 2.0 execution engine that has been automatically generated from formal Dafny specifications.

## Files

- `bpmn-engine.js` - The main JavaScript implementation (159KB, 3944 lines)
- `bpmn-engine-js.dtr` - Dafny translation record file
- `package.json` - Node.js package configuration
- `node_modules/` - JavaScript dependencies

## Features

### Formally Verified BPMN Semantics
- **Token-based execution model** with rigorous state management
- **Parallel gateway support** with verified fork/join semantics
- **Process state validation** with invariants and pre/post-conditions
- **Deadlock detection** and termination guarantees

### Supported BPMN Elements
- Start Events
- End Events  
- Tasks (User, Service, Manual)
- Parallel Gateways (Fork & Join)
- Sequence Flows
- Process Variables

### Generated Code Features
- Type-safe data structures translated from Dafny
- Immutable state transitions
- Comprehensive error handling
- Execution tracing and history

## Usage

```bash
# Install dependencies
npm install

# Run the engine
npm start
# or
node bpmn-engine.js
```

## Integration

To use this engine in your JavaScript application:

```javascript
const bpmnEngine = require('./bpmn-engine.js');

// The engine provides all BPMN execution capabilities
// through the generated module structure
```

## Verification

This code was generated from Dafny specifications that include:
- **State invariants** ensuring execution correctness
- **Termination proofs** for all execution paths  
- **Deadlock freedom** guarantees
- **Token lifecycle** verification

## Source

Generated from Dafny source files:
- `engine.dfy` - Core execution engine
- `token.dfy` - Token management
- `state.dfy` - Process state handling
- `process.dfy` - Process definition
- `Context.dfy` - Execution context
- `execution_init.dfy` - Process initialization
- `scheduling.dfy` - Token scheduling

## Compilation

Generated using:
```bash
dafny build --target:js --no-verify --allow-warnings -o generated/bpmn-engine engine.dfy
```

---

**Note**: This is generated code from formal specifications. For modifications, please edit the original Dafny source files and regenerate. 
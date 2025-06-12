# BPMN 2.0 Execution Engine (Generated from Dafny)

This directory contains a JavaScript implementation of a BPMN 2.0 execution engine that has been automatically generated from formal Dafny specifications.

## Files

- `engine.js` - The main JavaScript implementation (199KB, 4831 lines)
- `engine-js.dtr` - Dafny translation record file
- `json-to-process.js` - JSON BPMN model converter and test generator
- `package.json` - Node.js package configuration
- `tests/` - Test files and JSON BPMN models
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
- Gateways (Parallel, Exclusive)
- Sequence Flows with conditional expressions
- Process Variables and data handling
- Intermediate Events (Message, Timer, Signal, Error)

### Generated Code Features
- Type-safe data structures translated from Dafny
- Immutable state transitions
- Comprehensive error handling
- Execution tracing and history

## Usage

### Prerequisites
```bash
# Install dependencies
npm install
```

### Basic Usage
The engine processes BPMN models provided as JSON files and executes them with formal verification guarantees.

```javascript
const engine = require('./engine.js');

// The engine provides BPMN execution capabilities
// with state monitoring and error detection
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
dafny build --target:js --no-verify --allow-warnings -o generated/engine engine.dfy
```

## Testing

The testing system provides comprehensive BPMN model validation with execution monitoring.

### Single Test
```bash
# Step 1: Convert JSON BPMN model to executable test
node json-to-process.js tests/parsed_models_03.json

# Step 2: Run the generated test
node tests/generated-parsed_models_03.js
```

### Batch Testing
Process multiple JSON BPMN models automatically:

**Windows:**
```bash
# Process all JSON files in tests directory
run-test.bat

# Process first 3 files (for testing)
run-test-sample.bat
```

**PowerShell:**
```powershell
# Native PowerShell execution with colored output
.\run-test.ps1
```

### Test Features
- Automatic JSON file discovery in `tests/` directory
- Two-step processing: conversion then execution
- Comprehensive logging with timestamps
- State monitoring with visual indicators
- Error tracking and success/failure statistics
- Detailed execution traces saved to log files

### Log Files
Test execution logs are saved in the `tests/` directory with format:
- `test-execution-all-YYYYMMDD_HHMMSS.log` (full batch)
- `test-execution-sample-YYYYMMDD_HHMMSS.log` (sample batch)
- `test-execution-ps-YYYYMMDD_HHMMSS.log` (PowerShell)
---

**Note**: This is generated code from formal specifications. For modifications, please edit the original Dafny source files and regenerate. 
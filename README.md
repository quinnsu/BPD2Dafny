# BPD2Dafny: BPMN Process Definition to Dafny

A formal verification framework for Business Process Model and Notation (BPMN) 2.0 processes, providing end-to-end toolchain from BPMN model parsing to formally verified JavaScript execution engine.

## Overview

This project implements a complete toolchain for formal verification of BPMN processes:

```
BPMN XML → JSON → Dafny Specifications → Verified JavaScript Engine
```

The system ensures **mathematical correctness** and **deadlock freedom** of business process execution through formal verification techniques.

## Project Structure

```
BPD2Dafny/
├── bpmn-parser/           # BPMN XML to JSON parser (Python)
├── dafny/                 # Formal specifications and generated code
│   ├── src/               # Dafny source files
│   │   ├── engine.dfy     # Core execution engine (71KB, 1571 lines)
│   │   ├── token.dfy      # Token management (25KB, 738 lines)
│   │   ├── state.dfy      # Process state handling (20KB, 589 lines)
│   │   ├── scheduling.dfy # Token scheduling (15KB, 435 lines)
│   │   ├── Context.dfy    # Execution context (7.9KB, 244 lines)
│   │   ├── execution_init.dfy # Process initialization (8.7KB, 220 lines)
│   │   ├── process.dfy    # Process definition (1.3KB, 76 lines)
│   │   └── generated/     # Generated JavaScript engine
│   └── example/           # Example implementations
├── tests/                 # Test files and models
└── models/                # All the bpmn models

## Key Features

### Formal Verification
- **Token-based execution model** with mathematically proven correctness
- **Deadlock detection and prevention** with termination guarantees
- **State invariants** ensuring process consistency
- **Data conflict resolution** with formal concurrency control
- **Process completeness verification**

### BPMN 2.0 Support
- **Events**: Start, End, Intermediate (Message, Timer, Signal, Error)
- **Tasks**: User, Service, Manual with data handling
- **Gateways**: Parallel (Fork/Join), Exclusive with conditional flows
- **Process Variables**: Type-safe variable management
- **Sequence Flows**: Conditional expressions and routing

### Generated Execution Engine
- **Type-safe JavaScript** generated from Dafny specifications
- **Runtime state monitoring** with visual indicators
- **Comprehensive error handling** with detailed diagnostics
- **Execution tracing** and history management
- **Batch processing** capabilities with logging

## Quick Start

### Prerequisites
- Python 3.7+ (for BPMN parser)
- Dafny 4.0+ (for formal verification)
- Node.js (for JavaScript execution)

### Installation
```bash
# Clone the repository
git clone <repository-url>
cd BPD2Dafny

# Install Python dependencies for parser
cd bpmn-parser
pip install -r requirements.txt

# Install Node.js dependencies for execution engine
cd ../dafny/src/generated
npm install
```

### Basic Usage

#### 1. Parse BPMN Model
```bash
cd bpmn-parser
python parser_example.py models/your_model.bpmn
```

#### 2. Verify with Dafny
```bash
cd ../dafny/src
dafny verify engine.dfy
```

#### 3. Generate JavaScript Engine
```bash
dafny build --target:js --no-verify --allow-warnings -o generated/engine engine.dfy
```

#### 4. Test BPMN Process
```bash
cd generated
# Single test
node json-to-process.js tests/parsed_models_03.json
node tests/generated-parsed_models_03.js

# Batch testing
run-test.bat
```

## Testing Framework

### Automated Testing
- **Single Process Testing**: Convert and execute individual BPMN models
- **Batch Processing**: Automated testing of multiple models with logging
- **State Monitoring**: Real-time execution state tracking with visual indicators
- **Error Analysis**: Comprehensive error reporting and diagnostics

### Test Execution
```bash
# Windows batch processing
run-test.bat                    # Process all JSON files
run-test-sample.bat            # Process first 3 files (testing)

# PowerShell with colored output
.\run-test.ps1
```

### Log Files
Execution logs are automatically saved in `tests/` directory:
- `test-execution-all-YYYYMMDD_HHMMSS.log` (full batch)
- `test-execution-sample-YYYYMMDD_HHMMSS.log` (sample batch)
- `test-execution-ps-YYYYMMDD_HHMMSS.log` (PowerShell)

## Formal Verification Details

### Verification Properties
- **Safety**: No invalid state transitions
- **Liveness**: All processes eventually terminate or complete
- **Deadlock Freedom**: No circular token dependencies
- **Data Integrity**: Variable access conflicts are detected and resolved
- **Token Conservation**: Tokens are properly created, moved, and consumed

### Proof Structure
- **State Invariants**: Process states maintain consistency properties
- **Termination Proofs**: All execution paths have bounded completion
- **Concurrency Safety**: Parallel execution maintains process semantics
- **Error Handling**: All error conditions are formally specified

## Examples

- All models
## Components

### BPMN Parser (`bpmn-parser/`)
Python-based XML parser that converts BPMN 2.0 models to structured JSON format suitable for formal verification.

### Dafny Specifications (`dafny/src/`)
Formal specifications of BPMN execution semantics with mathematical proofs of correctness properties.

### Generated Engine (`dafny/src/generated/`)
JavaScript execution engine automatically generated from verified Dafny specifications, ensuring runtime correctness.



## Research Applications



## License



## Citation


---

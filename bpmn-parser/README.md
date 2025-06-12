# Parser
## Parse BPMN XML to JSON

This module is part of the BPD2DAFNY project, enabling parsing BPMN XML file to JSON file.

Our target is to realize a tool chain :

          
BPMN XML < - JSON -> Dafny object(java object/ js object /...)

And we will utilize the dafny-JSON library to support safe and verified deserialization.


## Structure


```
bpmn-parser/
├── bpmn_model.py          # model definition
├── bpmn_types.py          # type definition
├── env.py                 # environment
├── parser_example.py      # example
├── utils/                 # utils
│   ├── __init__.py
│   └── common.py        
├── models/               
│   └── model_01.bpmn  
└── README.md            
```

## Start

### 1. Environment

- Python 3.7+

### 2. Run

```bash
cd bpmn-parser

python parser_example.py

python parser_example.py model_01.bpmn

python parser_example.py --help
```

## Support elements

- **Event**
  - StartEvent 
  - EndEvent 

- **Tasks**
  - Task 
  - UserTask 
  - ServiceTask 
  - ManualTask 
  - SendTask 
  - CallActivity 
  - BusinessRule 

- **Gateways**
  - ParallelGateway
  - ExclusiveGateway

- **Flows**
  - SequenceFlow 

- **Proces）**
  - Process 



```python
from bpmn_model import BpmnModel

model = BpmnModel("your_model.bpmn")

elements = model.elements

user_tasks = model.get_elements_by_type("UserTask")

model_dict = model.to_dict()

json_file = model.export_parsed_data("custom_output.json")
```

### More elements to be supported


```python
@bpmn_tag("bpmn:newElementType")
class NewElementType(BpmnObject):
    def __init__(self):
        self.custom_property = None
    
    def parse(self, element):
        super().parse(element)
        self.custom_property = element.attrib.get("customAttr")
```

Based on the PYTHON-BPMN-Engine.
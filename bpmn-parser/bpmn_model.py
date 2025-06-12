import xml.etree.ElementTree as ET
from bpmn_types import (
    BPMN_MAPPINGS, NS, UserTask, SequenceFlow, Gateway, 
    ExclusiveGateway, ServiceTask, CallActivity, Task, 
    DataObject, DataObjectReference
)
from collections import defaultdict
import os
import json
from types import SimpleNamespace


class BpmnModel:
    
    def __init__(self, model_path):
        self.elements = {}
        self.flow = defaultdict(list)
        self.process_elements = {}
        self.main_collaboration_process = None
        self.model_path = model_path
        self.subprocesses = {}
        self.main_process = SimpleNamespace()

        self._parse_bpmn_file()

    def _parse_bpmn_file(self):
        try:
            if os.path.exists(self.model_path):
                file_path = self.model_path
            else:
                file_path = os.path.join("models", self.model_path)
                if not os.path.exists(file_path):
                    raise FileNotFoundError(f"BPMN file not found: {self.model_path}")
            
            model_tree = ET.parse(file_path)
            model_root = model_tree.getroot()
            processes = model_root.findall("bpmn:process", NS)
            
            for process in processes:
                self._parse_process(process, processes)
                
        except FileNotFoundError:
            raise FileNotFoundError(f"BPMN file not found: {self.model_path}")
        except ET.ParseError as e:
            raise ValueError(f"BPMN file parsing error: {e}")

    def _parse_process(self, process, all_processes):
        p = BPMN_MAPPINGS["bpmn:process"]()
        p.parse(process)
        self.process_elements[p._id] = {}
        
        if len(all_processes) > 1 and p.is_main_in_collaboration:
            self.main_collaboration_process = p._id
            self.main_process.name = p.name
            self.main_process.id = p._id
        else:
            self.main_process.name = p.name
            self.main_process.id = p._id
        
        # parse all elements in the process
        for tag, _type in BPMN_MAPPINGS.items():
            for e in process.findall(f"{tag}", NS):
                t = _type()
                t.parse(e)
                
                # handle special element types
                if isinstance(t, CallActivity):
                    self.subprocesses[t.called_element] = t.deployment
                if isinstance(t, SequenceFlow):
                    self.flow[t.source].append(t)
                
                self.elements[t._id] = t
                self.process_elements[p._id][t._id] = t

    def print_parsed_elements(self):
        print("=" * 80)
        print(f"BPMN model parsing result: {self.model_path}")
        print("=" * 80)
        
        print(f"\nMain process information:")
        print(f"  - Process ID: {self.main_process.id}")
        print(f"  - Process name: {self.main_process.name}")
        if self.main_collaboration_process:
            print(f"  - Collaboration main process: {self.main_collaboration_process}")
        
        # group elements by type
        elements_by_type = self._group_elements_by_type()
        
        # show elements by type
        for element_type, elements in elements_by_type.items():
            print(f"\n🔹 {element_type} ({len(elements)} elements):")
            for element in elements:
                self._print_element_details(element)
        
        # show flow information
        print(f"\nFlow information ({len(self.flow)} nodes):")
        for source_id, sequences in self.flow.items():
            source_element = self.elements.get(source_id)
            source_name = source_element.name if source_element and source_element.name else source_id
            print(f"  {source_name} ({source_id}):")
            for seq in sequences:
                target_element = self.elements.get(seq.target)
                target_name = target_element.name if target_element and target_element.name else seq.target
                condition_info = f" [Condition: {seq.condition}]" if seq.condition else ""
                print(f" {target_name} ({seq.target}){condition_info}")
        
        # show subprocess information
        if self.subprocesses:
            print(f"\nSubprocesses ({len(self.subprocesses)}):")
            for subprocess_id, deployment in self.subprocesses.items():
                deployment_info = f" (Deployment: {deployment})" if deployment else " (Embedded)"
                print(f"  - {subprocess_id}{deployment_info}")
        
        print("=" * 80)
    
    def _print_element_details(self, element):
        # print detailed information of a single element
        details = element.to_detailed_dict()
        name_info = f" - {details['name']}" if details['name'] else ""
        print(f"    • {details['_id']}{name_info}")
        
        # show special attributes
        if isinstance(element, SequenceFlow):
            print(f"      Source: {details['source']} → Target: {details['target']}")
            if details['condition']:
                print(f"      Condition: {details['condition']}")
        
        elif isinstance(element, UserTask):
            if details['form_fields']:
                print(f"      Form fields: {list(details['form_fields'].keys())}")
            if details['documentation']:
                print(f"      Documentation: {details['documentation']}")
        
        elif isinstance(element, ServiceTask):
            if details['input_variables']:
                print(f"      Input variables: {list(details['input_variables'].keys())}")
            if details['output_variables']:
                print(f"      Output variables: {list(details['output_variables'].keys())}")
            if details['connector_fields']['connector_id']:
                print(f"      Connector: {details['connector_fields']['connector_id']}")
        
        elif isinstance(element, Gateway):
            print(f"      Incoming: {details['incoming']}, Outgoing: {details['outgoing']}")
            if isinstance(element, ExclusiveGateway) and details['default']:
                print(f"      Default path: {details['default']}")
        
        elif isinstance(element, CallActivity):
            print(f"      Called element: {details['called_element']}")
            print(f"      Deployment mode: {details['deployment']}")
        
        # Show data associations for tasks
        if isinstance(element, Task):
            if details.get('data_input_associations'):
                print(f"      Data inputs: {[assoc['source_ref'] for assoc in details['data_input_associations'] if assoc['source_ref']]}")
            if details.get('data_output_associations'):
                print(f"      Data outputs: {[assoc['target_ref'] for assoc in details['data_output_associations'] if assoc['target_ref']]}")
        
        # Show data object information
        if isinstance(element, DataObjectReference):
            print(f"      Data object ref: {details['data_object_ref']}")
            if details['data_state']:
                print(f"      Data state: {details['data_state']}")
        
        elif isinstance(element, DataObject):
            if details['item_subject_ref']:
                print(f"      Item subject ref: {details['item_subject_ref']}")
            if details['is_collection']:
                print(f"      Is collection: {details['is_collection']}")

    def export_parsed_data(self, filename=None, output_dir=None):
        if not filename:
            # handle file path, replace special characters
            clean_path = self.model_path.replace('.bpmn', '.json').replace('/', '_').replace('\\', '_')
            filename = f"parsed_{clean_path}"
        
        # if output directory is specified, save the file to the directory
        if output_dir:
            filename = os.path.join(output_dir, os.path.basename(filename))
        
        export_data = {
            "model_path": self.model_path,
            "main_process": self.main_process.__dict__,
            "elements": {
                element_id: element.to_detailed_dict() 
                for element_id, element in self.elements.items()
            },
            "flow": {
                source_id: [
                    {
                        "sequence_id": seq._id,
                        "target": seq.target,
                        "condition": seq.condition,
                        "name": seq.name
                    }
                    for seq in sequences
                ]
                for source_id, sequences in self.flow.items()
            },
            "subprocesses": self.subprocesses,
            "statistics": {
                "total_elements": len(self.elements),
                "elements_by_type": {
                    element_type: len(elements)
                    for element_type, elements in self._group_elements_by_type().items()
                }
            },
            "process_elements": {
                process_id: list(elements.keys())
                for process_id, elements in self.process_elements.items()
            }
        }
        
        with open(filename, 'w', encoding='utf-8') as f:
            json.dump(export_data, f, indent=2, ensure_ascii=False)
        
        print(f"Parsing data exported to: {filename}")
        return filename
    
    def _group_elements_by_type(self):
        # group elements by type
        elements_by_type = {}
        for element in self.elements.values():
            element_type = type(element).__name__
            if element_type not in elements_by_type:
                elements_by_type[element_type] = []
            elements_by_type[element_type].append(element)
        return elements_by_type

    def get_element_by_id(self, element_id):
        # get element by id
        return self.elements.get(element_id)

    def get_elements_by_type(self, element_type):
        # get elements by type
        return [element for element in self.elements.values() 
                if type(element).__name__ == element_type]

    def to_dict(self):
        # return complete dictionary representation
        return {
            "model_path": self.model_path,
            "main_process": self.main_process.__dict__,
            "elements": {
                element_id: element.to_detailed_dict()
                for element_id, element in self.elements.items()
            },
            "flow": {
                source_id: [seq.to_detailed_dict() for seq in sequences]
                for source_id, sequences in self.flow.items()
            },
            "statistics": {
                "total_elements": len(self.elements),
                "elements_by_type": {
                    element_type: len(elements)
                    for element_type, elements in self._group_elements_by_type().items()
                }
            }
        } 

    def generate_task_data_info(self):
        task_data_info = {}
        tasks = self.get_elements_by_type("Task")
        
        for task in tasks:
            task_info = {
                "taskId": task._id,
                "taskName": task.name,
                "taskData": {
                    "inputVariables": [],
                    "outputVariables": []
                }
            }
            
            
            for input_assoc in task.data_input_associations:
                if input_assoc.source_ref:
                    data_obj_ref = self.get_element_by_id(input_assoc.source_ref)
                    if data_obj_ref:
                        input_var = {
                            "name": data_obj_ref.name or input_assoc.source_ref,
                            "type": "object",
                            "description": f": {data_obj_ref.name or input_assoc.source_ref}"
                        }
                        task_info["taskData"]["inputVariables"].append(input_var)
            
            for output_assoc in task.data_output_associations:
                if output_assoc.target_ref:
                    data_obj_ref = self.get_element_by_id(output_assoc.target_ref)
                    if data_obj_ref:
                        output_var = {
                            "name": data_obj_ref.name or output_assoc.target_ref,
                            "type": "object",
                            "description": f" {data_obj_ref.name or output_assoc.target_ref}"
                        }
                        task_info["taskData"]["outputVariables"].append(output_var)
 
            if task_info["taskData"]["inputVariables"] or task_info["taskData"]["outputVariables"]:
                task_data_info[task._id] = task_info
        
        return task_data_info

    def export_task_data_info(self, filename=None, output_dir=None):
        if not filename:
            clean_path = self.model_path.replace('.bpmn', '_task_data.json').replace('/', '_').replace('\\', '_')
            filename = f"task_data_{clean_path}"
        
        if output_dir:
            filename = os.path.join(output_dir, os.path.basename(filename))
        
        task_data_info = self.generate_task_data_info()
        
        with open(filename, 'w', encoding='utf-8') as f:
            json.dump(task_data_info, f, indent=2, ensure_ascii=False)

        return filename 
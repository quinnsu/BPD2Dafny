import requests
import os
import env
from utils.common import parse_expression

NS = {
    "bpmn": "http://www.omg.org/spec/BPMN/20100524/MODEL",
    "camunda": "http://camunda.org/schema/1.0/bpmn",
}

BPMN_MAPPINGS = {}


def bpmn_tag(tag):
    def wrap(object):
        object.tag = tag
        BPMN_MAPPINGS[tag] = object
        return object

    return wrap


class BpmnObject(object):
    def __repr__(self):
        return f"{type(self).__name__}({self.name or self._id})"

    def to_json(self):
        return {
            "_id": self._id,
            "name": self.name,
        }

    def to_detailed_dict(self):
        """返回对象的详细字典表示，包含所有属性"""
        result = {
            "class": type(self).__name__,
            "tag": getattr(self, 'tag', None),
            "_id": getattr(self, '_id', None),
            "name": getattr(self, 'name', None),
        }
        
        # 添加类特有的属性
        for attr_name in dir(self):
            if not attr_name.startswith('_') and attr_name not in ['tag', 'name', 'parse', 'run', 'to_json', 'to_detailed_dict', 'get_info']:
                attr_value = getattr(self, attr_name)
                if not callable(attr_value):
                    result[attr_name] = attr_value
        
        return result

    def parse(self, element):
        self._id = element.attrib["id"]
        self.name = element.attrib["name"] if "name" in element.attrib else None

    def run(self):
        return True


@bpmn_tag("bpmn:process")
class Process(BpmnObject):
    def __init__(self):
        self.is_main_in_collaboration = None
        self.name = None

    def parse(self, element):
        super(Process, self).parse(element)
        # Extensions should exists only if it's Collaboration diagram
        self.name = element.attrib["name"]
        if element.find(".bpmn:extensionElements", NS):
            ext = element.find(".bpmn:extensionElements", NS)
            for p in ext.findall(".//camunda:property", NS):
                # Find property is_main
                if p.attrib["name"] == "is_main" and p.attrib["value"] == "True":
                    self.is_main_in_collaboration = True


@bpmn_tag("bpmn:sequenceFlow")
class SequenceFlow(BpmnObject):
    def __init__(self):
        self.source = None
        self.target = None
        self.condition = None

    def parse(self, element):
        super(SequenceFlow, self).parse(element)
        self.source = element.attrib["sourceRef"]
        self.target = element.attrib["targetRef"]
        for c in element.findall("bpmn:conditionExpression", NS):
            self.condition = c.text

    def __repr__(self):
        condition = f" w. {len(self.condition)} con. " if self.condition else ""
        return f"{type(self).__name__}({self._id}): {self.source} -> {self.target}{condition}"

    def to_detailed_dict(self):
        result = super().to_detailed_dict()
        result.update({
            "source": self.source,
            "target": self.target,
            "condition": self.condition,
        })
        return result


@bpmn_tag("bpmn:task")
class Task(BpmnObject):
    def __init__(self):
        self.data_input_associations = []
        self.data_output_associations = []

    def parse(self, element):
        super(Task, self).parse(element)
        
        # Parse data input associations
        for dia in element.findall("bpmn:dataInputAssociation", NS):
            data_input_assoc = DataInputAssociation()
            data_input_assoc.parse(dia)
            self.data_input_associations.append(data_input_assoc)
        
        # Parse data output associations
        for doa in element.findall("bpmn:dataOutputAssociation", NS):
            data_output_assoc = DataOutputAssociation()
            data_output_assoc.parse(doa)
            self.data_output_associations.append(data_output_assoc)

    def get_info(self):
        return {"type": self.tag}

    def to_detailed_dict(self):
        result = super().to_detailed_dict()
        result.update({
            "data_input_associations": [assoc.to_detailed_dict() for assoc in self.data_input_associations],
            "data_output_associations": [assoc.to_detailed_dict() for assoc in self.data_output_associations],
        })
        return result


@bpmn_tag("bpmn:manualTask")
class ManualTask(Task):
    pass


@bpmn_tag("bpmn:userTask")
class UserTask(Task):
    def __init__(self):
        super(UserTask, self).__init__()
        self.form_fields = {}
        self.documentation = ""

    def parse(self, element):
        super(UserTask, self).parse(element)
        for f in element.findall(".//camunda:formField", NS):
            form_field_properties_dict = {}
            form_field_validations_dict = {}

            self.form_fields[f.attrib["id"]] = {}
            self.form_fields[f.attrib["id"]]["type"] = f.attrib["type"]
            if "label" in f.attrib:
                self.form_fields[f.attrib["id"]]["label"] = f.attrib["label"]
            else:
                self.form_fields[f.attrib["id"]]["label"] = ""

            for p in f.findall(".//camunda:property", NS):
                form_field_properties_dict[p.attrib["id"]] = parse_expression(
                    p.attrib["value"], env.SYSTEM_VARS | env.DS
                )

            for v in f.findall(".//camunda:constraint", NS):
                form_field_validations_dict[v.attrib["name"]] = v.attrib["config"]

            self.form_fields[f.attrib["id"]]["validation"] = form_field_validations_dict
            self.form_fields[f.attrib["id"]]["properties"] = form_field_properties_dict

        for d in element.findall(".//bpmn:documentation", NS):
            self.documentation = d.text

    def run(self, state, user_input):
        for k, v in user_input.items():
            if k in self.form_fields:
                state[k] = v
        return True

    def get_info(self):
        info = super(UserTask, self).get_info()
        return {
            **info,
            "form_fields": self.form_fields,
            "documentation": self.documentation,
        }

    def to_detailed_dict(self):
        result = super().to_detailed_dict()
        result.update({
            "form_fields": self.form_fields,
            "documentation": self.documentation,
        })
        return result


@bpmn_tag("bpmn:serviceTask")
class ServiceTask(Task):
    def __init__(self):
        super(ServiceTask, self).__init__()
        self.properties_fields = {}
        self.input_variables = {}
        self.output_variables = {}
        self.connector_fields = {
            "connector_id": "",
            "input_variables": {},
            "output_variables": {},
        }

    def parse(self, element):
        super(ServiceTask, self).parse(element)

        datasources = {}
        try:
            datasources = env.DS
        except Exception:
            print("No DS in env.py")

        for ee in element.findall(".//bpmn:extensionElements", NS):
            # Find direct children inputOutput, Input/Output tab in Camunda
            self._parse_input_output_variables(
                ee, self.input_variables, self.output_variables
            )
            # Find connector data, Connector tab in Camunda
            for con in ee.findall(".camunda:connector", NS):
                self._parse_input_output_variables(
                    con,
                    self.connector_fields["input_variables"],
                    self.connector_fields["output_variables"],
                )
                connector_id = con.find("camunda:connectorId", NS).text
                if connector_id in datasources:
                    ds = datasources[connector_id]
                    self.connector_fields["connector_id"] = ds["type"]
                    self.connector_fields["input_variables"]["base_url"] = ds["url"]

    def _parse_input_output_variables(self, element, input_dict, output_dict):
        for io in element.findall(".camunda:inputOutput", NS):
            for inparam in io.findall(".camunda:inputParameter", NS):
                self._parse_input_output_parameters(inparam, input_dict)
            for outparam in io.findall(".camunda:outputParameter", NS):
                self._parse_input_output_parameters(outparam, output_dict)

    def _parse_input_output_parameters(self, element, dictionary):
        if element.findall(".camunda:list", NS):
            helper_list = []
            for lv in element.find("camunda:list", NS):
                helper_list.append(lv.text) if lv.text else ""
            dictionary[element.attrib["name"]] = helper_list
        elif element.findall(".camunda:map", NS):
            helper_dict = {}
            for mv in element.find("camunda:map", NS):
                helper_dict[mv.attrib["key"]] = mv.text
            dictionary[element.attrib["name"]] = helper_dict
        elif element.findall(".camunda:script", NS):
            # script not supported
            pass
        else:
            dictionary[element.attrib["name"]] = element.text if element.text else ""

    def to_detailed_dict(self):
        result = super().to_detailed_dict()
        result.update({
            "input_variables": self.input_variables,
            "output_variables": self.output_variables,
            "connector_fields": self.connector_fields,
        })
        return result


@bpmn_tag("bpmn:sendTask")
class SendTask(ServiceTask):
    def parse(self, element):
        super(SendTask, self).parse(element)


@bpmn_tag("bpmn:callActivity")
class CallActivity(Task):
    def __init__(self):
        self.deployment = False
        self.called_element = ""

    def parse(self, element):
        super(CallActivity, self).parse(element)
        if element.attrib.get("calledElement"):
            self.called_element = element.attrib["calledElement"]
        if (
            element.attrib.get(f"{{{NS['camunda']}}}calledElementBinding")
            and element.attrib.get(f"{{{NS['camunda']}}}calledElementBinding")
            == "deployment"
        ):
            self.deployment = True

    def to_detailed_dict(self):
        result = super().to_detailed_dict()
        result.update({
            "deployment": self.deployment,
            "called_element": self.called_element,
        })
        return result


@bpmn_tag("bpmn:businessRule")
class BusinessRule(ServiceTask):
    def __init__(self):
        self.decision_ref = None

    def parse(self, element):
        super(BusinessRule, self).parse(element)


@bpmn_tag("bpmn:event")
class Event(BpmnObject):
    pass


@bpmn_tag("bpmn:startEvent")
class StartEvent(Event):
    pass


@bpmn_tag("bpmn:endEvent")
class EndEvent(Event):
    pass


@bpmn_tag("bpmn:gateway")
class Gateway(BpmnObject):
    def parse(self, element):
        self.incoming = len(element.findall("bpmn:incoming", NS))
        self.outgoing = len(element.findall("bpmn:outgoing", NS))
        super(Gateway, self).parse(element)

    def to_detailed_dict(self):
        result = super().to_detailed_dict()
        result.update({
            "incoming": self.incoming,
            "outgoing": self.outgoing,
        })
        return result


@bpmn_tag("bpmn:parallelGateway")
class ParallelGateway(Gateway):
    def add_token(self):
        self.incoming -= 1

    def run(self):
        return self.incoming == 0


@bpmn_tag("bpmn:exclusiveGateway")
class ExclusiveGateway(Gateway):
    def __init__(self):
        self.default = False
        super(ExclusiveGateway, self).__init__()

    def parse(self, element):
        self.default = (
            element.attrib["default"] if "default" in element.attrib else None
        )
        super(ExclusiveGateway, self).parse(element)

    def to_detailed_dict(self):
        result = super().to_detailed_dict()
        result.update({
            "default": self.default,
        })
        return result 


@bpmn_tag("bpmn:dataObject")
class DataObject(BpmnObject):
    def __init__(self):
        self.item_subject_ref = None
        self.is_collection = False

    def parse(self, element):
        super(DataObject, self).parse(element)
        if "itemSubjectRef" in element.attrib:
            self.item_subject_ref = element.attrib["itemSubjectRef"]
        if "isCollection" in element.attrib:
            self.is_collection = element.attrib["isCollection"].lower() == "true"

    def to_detailed_dict(self):
        result = super().to_detailed_dict()
        result.update({
            "item_subject_ref": self.item_subject_ref,
            "is_collection": self.is_collection,
        })
        return result


@bpmn_tag("bpmn:dataObjectReference")
class DataObjectReference(BpmnObject):
    def __init__(self):
        self.data_object_ref = None
        self.data_state = None

    def parse(self, element):
        super(DataObjectReference, self).parse(element)
        if "dataObjectRef" in element.attrib:
            self.data_object_ref = element.attrib["dataObjectRef"]
        
        # Parse data state if exists
        data_state_elem = element.find("bpmn:dataState", NS)
        if data_state_elem is not None:
            self.data_state = data_state_elem.attrib.get("name")

    def to_detailed_dict(self):
        result = super().to_detailed_dict()
        result.update({
            "data_object_ref": self.data_object_ref,
            "data_state": self.data_state,
        })
        return result


@bpmn_tag("bpmn:dataInputAssociation")
class DataInputAssociation(BpmnObject):
    def __init__(self):
        self.source_ref = None
        self.target_ref = None
        self.transformation = None

    def parse(self, element):
        super(DataInputAssociation, self).parse(element)
        
        # Parse source reference
        source_elem = element.find("bpmn:sourceRef", NS)
        if source_elem is not None:
            self.source_ref = source_elem.text
        
        # Parse target reference
        target_elem = element.find("bpmn:targetRef", NS)
        if target_elem is not None:
            self.target_ref = target_elem.text
        
        # Parse transformation if exists
        transform_elem = element.find("bpmn:transformation", NS)
        if transform_elem is not None:
            self.transformation = transform_elem.text

    def to_detailed_dict(self):
        result = super().to_detailed_dict()
        result.update({
            "source_ref": self.source_ref,
            "target_ref": self.target_ref,
            "transformation": self.transformation,
        })
        return result


@bpmn_tag("bpmn:dataOutputAssociation")
class DataOutputAssociation(BpmnObject):
    def __init__(self):
        self.source_ref = None
        self.target_ref = None
        self.transformation = None

    def parse(self, element):
        super(DataOutputAssociation, self).parse(element)
        
        # Parse source reference
        source_elem = element.find("bpmn:sourceRef", NS)
        if source_elem is not None:
            self.source_ref = source_elem.text
        
        # Parse target reference
        target_elem = element.find("bpmn:targetRef", NS)
        if target_elem is not None:
            self.target_ref = target_elem.text
        
        # Parse transformation if exists
        transform_elem = element.find("bpmn:transformation", NS)
        if transform_elem is not None:
            self.transformation = transform_elem.text

    def to_detailed_dict(self):
        result = super().to_detailed_dict()
        result.update({
            "source_ref": self.source_ref,
            "target_ref": self.target_ref,
            "transformation": self.transformation,
        })
        return result 
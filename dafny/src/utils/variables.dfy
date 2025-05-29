/**
  * BPMN variable management module
  */
include "option.dfy"
module Variables {
  import opened Optional

  /**
    * variable value type
    */
  datatype VariableValue =
    | StringValue(stringValue: string)
    | IntValue(intValue: int)
    | BoolValue(boolValue: bool)
    | ListValue(values: seq<VariableValue>)
    | ObjectValue(fields: map<string, VariableValue>)

  /**
    * variable map
    */
  type VariableMap = map<string, VariableValue>

  /**
    * create an empty variable map
    */
  function EmptyVariables(): VariableMap {
    map[]
  }

  /**
    * set variable value
    */
  function SetVariable(vars: VariableMap, name: string, value: VariableValue): VariableMap {
    vars[name := value]
  }

  /**
    * get variable value
    */
  function GetVariable(vars: VariableMap, name: string): Option<VariableValue> {
    if name in vars then Some(vars[name]) else None
  }
}

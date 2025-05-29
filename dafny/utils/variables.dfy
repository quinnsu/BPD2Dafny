/**
  * BPMN 变量管理模块
  */
include "option.dfy"
module Variables {
  import opened Optional

  /**
    * 变量值类型
    */
  datatype VariableValue =
    | StringValue(stringValue: string)
    | IntValue(intValue: int)
    | BoolValue(boolValue: bool)
    | ListValue(values: seq<VariableValue>)
    | ObjectValue(fields: map<string, VariableValue>)

  /**
    * 变量映射
    */
  type VariableMap = map<string, VariableValue>

  /**
    * 创建空变量映射
    */
  function EmptyVariables(): VariableMap {
    map[]
  }

  /**
    * 设置变量值
    */
  function SetVariable(vars: VariableMap, name: string, value: VariableValue): VariableMap {
    vars[name := value]
  }

  /**
    * 获取变量值
    */
  function GetVariable(vars: VariableMap, name: string): Option<VariableValue> {
    if name in vars then Some(vars[name]) else None
  }
}

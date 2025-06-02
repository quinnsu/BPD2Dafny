/*
 * Execution Context - 执行上下文
 */
include "token.dfy"

module ExecutionContext {
  import opened Token

  /**
    * 执行上下文 - 最小化设计，保留关键信息
    */
  datatype Context = ExecutionContext(
    currentNodes: set<string>,        // 当前所有活跃token的位置（核心信息）
    lastExecutedNode: string,         // 最后执行的节点（用于调试）
    executionStep: nat                // 执行步数（用于监控）
  )

  /**
    * 创建初始执行上下文
    */
  function CreateInitialContext(): Context
  {
    ExecutionContext(
      currentNodes := {},
      lastExecutedNode := "",
      executionStep := 0
    )
  }

  /**
    * 更新执行上下文
    */
  function UpdateContext(
    context: Context,
    newCurrentNodes: set<string>,
    lastNode: string
  ): Context
  {
    ExecutionContext(
      currentNodes := newCurrentNodes,
      lastExecutedNode := lastNode,
      executionStep := context.executionStep + 1
    )
  }

  /**
    * 从token集合计算执行上下文
    */
  function ComputeContext(
    tokenCollection: Token.Collection,
    lastExecutedNode: string,
    previousContext: Context
  ): Context
  {
    var activeTokens := Token.GetActiveTokens(tokenCollection);
    var currentNodes := set tokenId | tokenId in activeTokens :: tokenCollection.tokens[tokenId].location;

    UpdateContext(
      previousContext,
      currentNodes,
      lastExecutedNode
    )
  }

  /**
    * 检查上下文是否有效
    */
  predicate ValidContext(context: Context)
  {
    context.executionStep >= 0
  }
} 
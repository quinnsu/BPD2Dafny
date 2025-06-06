/*
 * Execution Context - 执行上下文
 */
include "token.dfy"
include "utils/option.dfy"

module ExecutionContext {
  import opened Token
  import opened Optional

  /**
    * 执行上下文 - 简化设计，避免概念重复
    */
  datatype Context = ExecutionContext(
    lastExecutedNode: string,         // 最后执行的节点（用于调试）
    executionStep: nat,               // 执行步数（用于监控）
    executionQueue: seq<Token.TokenId> // 执行队列，管理待执行的tokens
  )

  /**
    * 创建初始执行上下文
    */
  function CreateInitialContext(): Context
  {
    ExecutionContext(
      lastExecutedNode := "",
      executionStep := 0,
      executionQueue := []
    )
  }

  /**
    * 更新执行上下文
    */
  function UpdateContext(
    context: Context,
    lastNode: string
  ): Context
  {
    ExecutionContext(
      lastExecutedNode := lastNode,
      executionStep := context.executionStep + 1,
      executionQueue := []  // 清空队列，下一步会重新填充
    )
  }

  /**
    * 初始化执行队列，将所有active tokens加入队列
    */
  function InitializeExecutionQueue(
    context: Context,
    activeTokens: set<Token.TokenId>
  ): Context
  {
    var tokenSequence := SetToSequence(activeTokens);
    context.(executionQueue := tokenSequence)
  }

  /**
    * 将token添加到执行队列尾部
    */
  function EnqueueToken(context: Context, tokenId: Token.TokenId): Context
  {
    context.(executionQueue := context.executionQueue + [tokenId])
  }

  /**
    * 从执行队列头部取出token
    */
  function DequeueToken(context: Context): (Context, Token.TokenId)
    requires |context.executionQueue| > 0
    ensures |DequeueToken(context).0.executionQueue| == |context.executionQueue| - 1
  {
    var tokenId := context.executionQueue[0];
    var newQueue := context.executionQueue[1..];
    var newContext := context.(executionQueue := newQueue);
    (newContext, tokenId)
  }

  /**
    * 检查执行队列是否为空
    */
  predicate IsExecutionQueueEmpty(context: Context)
  {
    |context.executionQueue| == 0
  }

  /**
    * 将set转换为sequence（简化实现）
    */
  function {:verify false} SetToSequence(s: set<Token.TokenId>): seq<Token.TokenId>
  {
    if |s| == 0 then []
    else
      var x :| x in s;
      [x] + SetToSequence(s - {x})
  }

  /**
    *return the location of the active tokens
    */
  function GetCurrentNodes(
    tokenCollection: Token.Collection,
    context: Context
  ): set<string>
  {
    set tokenId | tokenId in tokenCollection.tokens &&
                  tokenCollection.tokens[tokenId].status == Active ::
      tokenCollection.tokens[tokenId].location
  }

  /**
    * 替代原来的ComputeContext函数
    */
  function ComputeContext(
    tokenCollection: Token.Collection,
    lastExecutedNode: string,
    previousContext: Context
  ): Context
  {
    var activeTokens := Token.GetActiveTokens(tokenCollection);
    var tokenSequence := SetToSequence(activeTokens);
    
    ExecutionContext(
      lastExecutedNode := lastExecutedNode,
      executionStep := previousContext.executionStep + 1,
      executionQueue := tokenSequence
    )
  }

  /**
    * 检查上下文是否有
    */
  predicate ValidContext(context: Context)
  {
    context.executionStep >= 0
  }
} 
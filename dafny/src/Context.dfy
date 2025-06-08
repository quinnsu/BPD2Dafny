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
    * 将set转换为sequence（建立元素等价关系）
    */
  function SetToSequence(s: set<Token.TokenId>): seq<Token.TokenId>
    ensures |SetToSequence(s)| == |s|
    ensures forall tokenId :: tokenId in s <==> tokenId in SetToSequence(s)
    decreases |s|
  {
    if |s| == 0 then []
    else
      var x := Token.PickOne(s);
      [x] + SetToSequence(s - {x})
  }

  /**
    *return the location of the active tokens
    */
  function {:opaque} GetCurrentNodes(
    tokenCollection: Token.Collection ): set<string>
    requires Token.ValidTokenCollection(tokenCollection)
    ensures   // 确保返回的位置对应于active tokens的位置
            forall location :: location in GetCurrentNodes(tokenCollection) <==> 
              (exists tokenId :: tokenId in Token.GetActiveTokens(tokenCollection) &&
                                 tokenCollection.tokens[tokenId].location == location)
    ensures   // 如果有active token在某位置，则该位置在结果中
            forall tokenId :: tokenId in Token.GetActiveTokens(tokenCollection) ==>
              tokenCollection.tokens[tokenId].location in GetCurrentNodes(tokenCollection)
  {
    set tokenId | tokenId in Token.GetActiveTokens(tokenCollection) ::
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
    requires Token.ValidTokenCollection(tokenCollection)
    requires ValidContext(previousContext)
    ensures ValidContext(ComputeContext(tokenCollection, lastExecutedNode, previousContext))
    ensures forall tokenId :: tokenId in ComputeContext(tokenCollection, lastExecutedNode, previousContext).executionQueue ==>
                        tokenId in Token.GetActiveTokens(tokenCollection)
    ensures forall tokenId :: tokenId in Token.GetActiveTokens(tokenCollection) ==>
                        tokenId in ComputeContext(tokenCollection, lastExecutedNode, previousContext).executionQueue
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

  /**
    * 检查上下文与token集合的一致性
    * 核心不变式：executionQueue中的所有token都必须在tokenCollection中且为Active状态
    */
  predicate ValidContextWithTokens(context: Context, tokenCollection: Token.Collection)
  {
    ValidContext(context) &&
    // 执行队列中的所有token都存在于token集合中
    (forall tokenId :: tokenId in context.executionQueue ==> 
       tokenId in tokenCollection.tokens) &&
    // 执行队列中的所有token都是Active状态
    (forall tokenId :: tokenId in context.executionQueue ==> 
       tokenCollection.tokens[tokenId].status == Active) &&
    // 所有Active token都在执行队列中（双向一致性）
    (forall tokenId :: tokenId in tokenCollection.tokens && 
                       tokenCollection.tokens[tokenId].status == Active ==> 
       tokenId in context.executionQueue)
  }

  /**
    * 创建一致的执行上下文（从token集合同步）
    */
  function CreateConsistentContext(
    tokenCollection: Token.Collection,
    lastExecutedNode: string,
    executionStep: nat
  ): Context
    requires Token.ValidTokenCollection(tokenCollection)
    ensures ValidContext(CreateConsistentContext(tokenCollection, lastExecutedNode, executionStep))
    ensures forall tokenId :: tokenId in Token.GetActiveTokens(tokenCollection) ==>
                        tokenId in CreateConsistentContext(tokenCollection, lastExecutedNode, executionStep).executionQueue
  {
    var activeTokens := Token.GetActiveTokens(tokenCollection);
    var tokenSequence := SetToSequence(activeTokens);
    
    ExecutionContext(
      lastExecutedNode := lastExecutedNode,
      executionStep := executionStep,
      executionQueue := tokenSequence
    )
  }

  /**
    * 安全的Token入队操作 - 只允许Active token入队
    */
  function SafeEnqueueToken(
    context: Context, 
    tokenId: Token.TokenId, 
    tokenCollection: Token.Collection
  ): Context
    requires ValidContext(context)
    requires tokenId in tokenCollection.tokens
    requires tokenCollection.tokens[tokenId].status == Active
    // 前置条件：当前队列中的token都是active的
    requires forall tid :: tid in context.executionQueue ==> 
               tid in tokenCollection.tokens && tokenCollection.tokens[tid].status == Active
    ensures var result := SafeEnqueueToken(context, tokenId, tokenCollection);
            ValidContext(result) &&
            // 新队列中的所有token都是active的
            (forall tid :: tid in result.executionQueue ==> 
               tid in tokenCollection.tokens && tokenCollection.tokens[tid].status == Active)
  {
    context.(executionQueue := context.executionQueue + [tokenId])
  }

  /**
    * 安全的Token出队操作 - 维护一致性
    */
  function SafeDequeueToken(
    context: Context,
    tokenCollection: Token.Collection
  ): (Context, Token.TokenId)
    requires ValidContext(context)
    requires |context.executionQueue| > 0
    // 前置条件：队列中的token都在集合中且为active
    requires forall tid :: tid in context.executionQueue ==> 
               tid in tokenCollection.tokens && tokenCollection.tokens[tid].status == Active
    ensures var (newContext, tokenId) := SafeDequeueToken(context, tokenCollection);
            ValidContext(newContext) &&
            tokenId in tokenCollection.tokens &&
            tokenCollection.tokens[tokenId].status == Active &&
            |newContext.executionQueue| == |context.executionQueue| - 1 &&
            tokenId == context.executionQueue[0]
  {
    var tokenId := context.executionQueue[0];
    var newQueue := context.executionQueue[1..];
    var newContext := context.(executionQueue := newQueue);
    (newContext, tokenId)
  }
} 
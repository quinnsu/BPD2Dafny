/*
 * Execution Context - 执行上下文
 */
include "token.dfy"
include "utils/option.dfy"
include "utils/Seq.dfy"

module ExecutionContext {
  import opened Token
  import opened Optional
  import opened Seq


  datatype Context = ExecutionContext(
    lastExecutedNode: string,         
    executionStep: nat,               
    executionQueue: seq<Token.TokenId> 
  )


  function CreateInitialContext(): Context
  {
    ExecutionContext(
      lastExecutedNode := "",
      executionStep := 0,
      executionQueue := []
    )
  }




  function InitializeExecutionQueue(
    context: Context,
    activeTokens: set<Token.TokenId>
  ): Context
  {
    var tokenSequence := SetToSequence(activeTokens);
    context.(executionQueue := tokenSequence)
  }


  function EnqueueToken(context: Context, tokenId: Token.TokenId): Context
  {
    context.(executionQueue := context.executionQueue + [tokenId])
  }


  function DequeueToken(context: Context): (Context, Token.TokenId)
    requires |context.executionQueue| > 0
    ensures |DequeueToken(context).0.executionQueue| == |context.executionQueue| - 1
  {
    var tokenId := Seq.First(context.executionQueue);
    var newQueue := Seq.DropFirst(context.executionQueue);
    var newContext := context.(executionQueue := newQueue);
    (newContext, tokenId)
  }


  function PeekFirstToken(context: Context): Token.TokenId
    requires |context.executionQueue| > 0
  {
    Seq.First(context.executionQueue)
  }



  function PeekLastToken(context: Context): Token.TokenId
    requires |context.executionQueue| > 0
  {
    Seq.Last(context.executionQueue)
  }



  function FilterExecutionQueue(
    context: Context, 
    isValid: Token.TokenId -> bool
  ): seq<Token.TokenId>
  {
    FilterExecutionQueueHelper(context.executionQueue, isValid)
  }


  function FilterExecutionQueueHelper(
    queue: seq<Token.TokenId>,
    isValid: Token.TokenId -> bool
  ): seq<Token.TokenId>
    decreases |queue|
  {
    if |queue| == 0 then []
    else
      var first := queue[0];
      var rest := FilterExecutionQueueHelper(queue[1..], isValid);
      if isValid(first) then [first] + rest else rest
  }


  predicate IsExecutionQueueEmpty(context: Context)
  {
    |context.executionQueue| == 0
  }


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


  function {:opaque} GetCurrentNodes(
    tokenCollection: Token.Collection ): set<string>
    requires Token.ValidTokenCollection(tokenCollection)
    ensures  
            forall location :: location in GetCurrentNodes(tokenCollection) <==> 
              (exists tokenId :: tokenId in Token.GetActiveTokens(tokenCollection) &&
                                 tokenCollection.tokens[tokenId].location == location)
    ensures  
            forall tokenId :: tokenId in Token.GetActiveTokens(tokenCollection) ==>
              tokenCollection.tokens[tokenId].location in GetCurrentNodes(tokenCollection)
  {
    set tokenId | tokenId in Token.GetActiveTokens(tokenCollection) ::
      tokenCollection.tokens[tokenId].location
  }


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


  predicate ValidContext(context: Context)
  {
    context.executionStep >= 0
  }


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
            tokenId == Seq.First(context.executionQueue)
  {
    var tokenId := Seq.First(context.executionQueue);
    var newQueue := Seq.DropFirst(context.executionQueue);
    var newContext := context.(executionQueue := newQueue);
    (newContext, tokenId)
  }
} 
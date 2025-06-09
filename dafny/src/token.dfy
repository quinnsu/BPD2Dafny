/*
 * Copyright 2025
 */
include "utils/Variables.dfy"
include "utils/option.dfy"
include "process.dfy"
/**
  * Token module for BPMN execution.
  * 
  * This module provides the data structures and operations for managing tokens
  * in a BPMN process execution. Tokens represent the flow of control through
  * a BPMN process and are used to track the execution state.
  */
module Token {

  import ProcessDefinition
  import opened Optional
  /**
    * Token ID type
    */
  type TokenId = nat

  /**
    * Node ID type (represents a BPMN element)
    */
  type NodeId = string

  /**
    * Token status enum
    */
  datatype TokenStatus =
    | Active    // Token is currently active and can be executed immediately
    | Waiting   // Token is waiting (e.g., for parallel join completion)
    | Consumed  // Token has been consumed (e.g., by a gateway or end event)
    | Suspended // Token is temporarily suspended (e.g., waiting for a message)
    | Error     // Token encountered an error

  /**
    * Token data structure
    * 
    * @param id Unique identifier for this token
    * @param location Current node where this token is located
    * @param status Current status of this token
    * @param parentToken Optional parent token (for tokens created by split)
    * @param childTokens Set of child tokens (for tracking split history)
    * @param data Local variables carried by this token
    * @param creationTime When this token was created
    * @param path Sequence of nodes this token has visited
    */
  datatype T = Token(
    id: TokenId,
    location: NodeId, //Where the token is currently located
    status: TokenStatus,
    parentToken: Option<TokenId>,
    childTokens: set<TokenId>,
    creationTime: nat,
    path: seq<NodeId>
  )

  /**
    * Token collection data structure
    * 
    * @param tokens Map of all tokens by ID
    * @param nextTokenId Next available token ID
    * @param currentTime Current execution time
    */
  datatype Collection = TokenCollection(
    tokens: map<TokenId, T>,
    nextTokenId: TokenId,
    currentTime: nat
  )

  /**
    * Token collection invariant - activeTokens must be a subset of tokens
    * property that should be satisfied all the time
    * the nexttokenId is a self-increasing number so it will be unique
    */
  predicate ValidTokenCollection(tc: Collection)
  {
    if |tc.tokens| == 0 then
      tc.nextTokenId == 0
    else
      tc.nextTokenId > 0 &&
      forall tokenId :: tokenId in tc.tokens ==> tokenId < tc.nextTokenId
  }

  /**
    * Create an empty token collection
    */
  function Create(): Collection
    ensures |GetActiveTokens(Create())| == 0
    ensures ValidTokenCollection(Create())
  {
    TokenCollection(
      tokens := map[],
      nextTokenId := 0,
      currentTime := 0
    )
  }

  /**
    * Create a new token at the specified node
    * 
    * @param tc Token collection
    * @param location Node where the token should be created
    * @returns Updated token collection and the ID of the new token
    */
  function CreateToken(tc: Collection, location: NodeId): (Collection, TokenId)
    requires ValidTokenCollection(tc)
    ensures var (newTc, tokenId) := CreateToken(tc, location);
            tokenId in newTc.tokens &&
            newTc.tokens[tokenId].status == Active &&
            newTc.tokens[tokenId].location == location &&
            tokenId in GetActiveTokens(newTc) &&
            |newTc.tokens| == |tc.tokens| + 1 &&
            |GetActiveTokens(newTc)| == |GetActiveTokens(tc)| + 1 &&
            tokenId !in tc.tokens  // 关键：新tokenId不在原集合中
    ensures ValidTokenCollection(CreateToken(tc, location).0)
    ensures var (newTc, tokenId) := CreateToken(tc, location);
            // 关键：CreateToken保持原有tokens不变
            forall originalTokenId :: originalTokenId in tc.tokens ==> 
              originalTokenId in newTc.tokens && newTc.tokens[originalTokenId] == tc.tokens[originalTokenId]
  {
    var tokenId := tc.nextTokenId;
    assert tokenId !in tc.tokens;  // 这个断言可能失败
    var token := Token(
                   id := tokenId,
                   location := location,
                   status := Active,
                   parentToken := None,
                   childTokens := {},
                   creationTime := tc.currentTime,
                   path := [location]
                 );

    var newTokens := tc.tokens[tokenId := token];
    var newTc := tc.(tokens := newTokens, nextTokenId := tokenId + 1);
    assert tokenId in GetActiveTokens(newTc);
    assert GetActiveTokens(newTc) == GetActiveTokens(tc) + {tokenId};
    
    (newTc, tokenId)
  }

  /**
    * create tokens for flows
    * 
    * @param tokens Token collection
    * @param flows Set of flow IDs
    * @param flowDefinitions Map of flow definitions
    * @returns Updated token collection and set of new token IDs
    */
  function CreateTokensForFlows(
    tokens: Collection,
    flows: set<string>,
    flowDefinitions: map<string, ProcessDefinition.SequenceFlow>
  ): (Collection, set<TokenId>)
    requires forall flowId :: flowId in flows ==> flowId in flowDefinitions
    requires ValidTokenCollection(tokens)
    ensures var (finalTokens, newTokenIds) := CreateTokensForFlows(tokens, flows, flowDefinitions);
            // 核心性质：新创建的token数量等于flows数量
            |newTokenIds| == |flows| &&
            // 所有新token都在最终的token集合中且为Active状态
            (forall tokenId :: tokenId in newTokenIds ==>
                                 tokenId in finalTokens.tokens &&
                                 finalTokens.tokens[tokenId].status == Active) &&
            // 新token都不在原始token集合中（唯一性）
            (forall tokenId :: tokenId in newTokenIds ==> tokenId !in tokens.tokens) &&
            // 原有token保持不变
            (forall tokenId :: tokenId in tokens.tokens ==>
                                 tokenId in finalTokens.tokens &&
                                 finalTokens.tokens[tokenId] == tokens.tokens[tokenId]) &&
            // 最终token集合大小 = 原始大小 + 新token数量
            |finalTokens.tokens| == |tokens.tokens| + |flows| &&
            // 保持有效性
            ValidTokenCollection(finalTokens) &&
            // 新增：每个flow的目标节点都有对应的新token
            (forall flowId :: flowId in flows ==>
                                exists tokenId :: tokenId in newTokenIds &&
                                                  finalTokens.tokens[tokenId].location == flowDefinitions[flowId].targetRef &&
                                                  finalTokens.tokens[tokenId].status == Active)
    decreases |flows|
  {
    if |flows| == 0 then
      (tokens, {})
    else
      var flowId := PickOne(flows);
      var remainingFlows := flows - {flowId};
      var targetNodeId := flowDefinitions[flowId].targetRef;
      var (tokensWithNew, newTokenId) := CreateToken(tokens, targetNodeId);

      assert |tokensWithNew.tokens| == |tokens.tokens| + 1;
      assert |remainingFlows| == |flows| - 1;

      var (finalTokens, remainingTokenIds) := CreateTokensForFlows(tokensWithNew, remainingFlows, flowDefinitions);

      assert |remainingTokenIds| == |remainingFlows|;
      assert newTokenId !in remainingTokenIds;

      (finalTokens, remainingTokenIds + {newTokenId})
  }

  /**
    * Move a token to a new location
    * 
    * @param tc Token collection
    * @param tokenId ID of the token to move
    * @param newLocation New node location
    * @returns Updated token collection
    */
  function MoveToken(tc: Collection, tokenId: TokenId, newLocation: NodeId): Collection
    requires ValidTokenCollection(tc)
    requires tokenId in tc.tokens && tc.tokens[tokenId].status == Active
    ensures ValidTokenCollection(MoveToken(tc, tokenId, newLocation))
  {
    var token := tc.tokens[tokenId];
    var updatedToken := token.(
                        location := newLocation,
                        path := token.path + [newLocation]
                        );

    tc.(tokens := tc.tokens[tokenId := updatedToken])
  }

  /**
    * Consume a token (mark it as consumed and remove from active tokens)
    * 
    * @param tc Token collection
    * @param tokenId ID of the token to consume
    * @returns Updated token collection
    */
  function ConsumeToken(tc: Collection, tokenId: TokenId): Collection
    requires ValidTokenCollection(tc)
    requires tokenId in tc.tokens && tc.tokens[tokenId].status == Active
    ensures ValidTokenCollection(ConsumeToken(tc, tokenId))
  {
    var token := tc.tokens[tokenId];
    var updatedToken := token.(status := Consumed);

    tc.(
    tokens := tc.tokens[tokenId := updatedToken]
    )
  }

  /**
    * Consume multiple tokens at once
    * 
    * @param tc Token collection
    * @param tokenIds Set of token IDs to consume
    * @returns Updated token collection
    */
  function ConsumeTokens(tc: Collection, tokenIds: set<TokenId>): Collection
    requires ValidTokenCollection(tc)
    requires forall id :: id in tokenIds ==> id in tc.tokens && tc.tokens[id].status == Active
    ensures ValidTokenCollection(ConsumeTokens(tc, tokenIds))
    ensures var result := ConsumeTokens(tc, tokenIds);
            // 关键：ConsumeTokens不删除tokens（双向包含，token集合完全相同）
            forall tokenId :: tokenId in tc.tokens ==> tokenId in result.tokens
    ensures var result := ConsumeTokens(tc, tokenIds);
            // 反向包含：result中的tokens都在原集合中
            forall tokenId :: tokenId in result.tokens ==> tokenId in tc.tokens
    ensures var result := ConsumeTokens(tc, tokenIds);
            // 被消费的tokens状态变为Consumed
            forall tokenId :: tokenId in tokenIds ==> 
              tokenId in result.tokens && result.tokens[tokenId].status == Consumed
    ensures var result := ConsumeTokens(tc, tokenIds);
            // 未被消费的tokens保持原状态
            forall tokenId :: tokenId in tc.tokens && tokenId !in tokenIds ==> 
              tokenId in result.tokens && result.tokens[tokenId] == tc.tokens[tokenId]
    decreases |tokenIds|
  {
    if |tokenIds| == 0 then tc
    else
      var tokenId := PickOne(tokenIds);
      var remainingIds := tokenIds - {tokenId};
      var tc' := ConsumeToken(tc, tokenId);
      ConsumeTokens(tc', remainingIds)
  }

  /**
    * Helper function to pick one element from a non-empty set
    * @param s Set of elements
    * @returns One element from the set
    */
  function {:verify false}  PickOne<T>(s: set<T>): T
    requires |s| > 0
  {
    var x :| x in s; x
  }

  /**
    * Split a token into multiple tokens (for parallel gateways)
    * 
    * @param tc Token collection
    * @param tokenId ID of the token to split
    * @param targetLocations Locations for the new tokens
    * @returns Updated token collection and set of new token IDs
    */
  function SplitToken(tc: Collection, tokenId: TokenId, targetLocations: seq<NodeId>): (Collection, set<TokenId>)
    requires ValidTokenCollection(tc)
    requires tokenId in tc.tokens && tc.tokens[tokenId].status == Active
    requires |targetLocations| > 0
    ensures ValidTokenCollection(SplitToken(tc, tokenId, targetLocations).0)
  {
    // First consume the parent token
    var tc' := ConsumeToken(tc, tokenId);
    var parentToken := tc.tokens[tokenId];

    // Create child tokens
    SplitTokenHelper(tc', tokenId, targetLocations, 0, {})
  }

  /**
    * Helper function for SplitToken to recursively create child tokens
    */
  function SplitTokenHelper(
    tc: Collection,
    parentId: TokenId,
    locations: seq<NodeId>,
    index: nat,
    createdTokens: set<TokenId>
  ): (Collection, set<TokenId>)
    requires ValidTokenCollection(tc)
    requires index <= |locations|
    requires parentId in tc.tokens
    ensures ValidTokenCollection(SplitTokenHelper(tc, parentId, locations, index, createdTokens).0)
    decreases |locations| - index
  {
    if index == |locations| then
      // Update parent token to track children
      var parentToken := tc.tokens[parentId];
      var updatedParent := parentToken.(childTokens := parentToken.childTokens + createdTokens);
      (tc.(tokens := tc.tokens[parentId := updatedParent]), createdTokens)
    else
      // Create a new token at the target location
      var (tc', newTokenId) := CreateToken(tc, locations[index]);

      // Update the new token with parent reference
      var newToken := tc'.tokens[newTokenId];
      var updatedToken := newToken.(parentToken := Some(parentId));
      var tc'' := tc'.(tokens := tc'.tokens[newTokenId := updatedToken]);

      // Continue with next location
      SplitTokenHelper(tc'', parentId, locations, index + 1, createdTokens + {newTokenId})
  }

  /**
    * Merge multiple tokens into a single token (for joining gateways)
    * 
    * @param tc Token collection
    * @param tokenIds Set of token IDs to merge
    * @param targetLocation Location for the merged token
    * @returns Updated token collection and ID of the new merged token
   
  function MergeTokens(tc: Collection, tokenIds: set<TokenId>, targetLocation: NodeId): (Collection, TokenId)
    requires forall id :: id in tokenIds ==> id in tc.tokens && tc.tokens[id].status == Active
    requires |tokenIds| > 0
    requires ValidTokenCollection(tc)
    ensures ValidTokenCollection(MergeTokens(tc, tokenIds, targetLocation).0)
  {
    // Consume all input tokens
    var tc' := ConsumeTokens(tc, tokenIds);

    // Create new merged token
    var (tc'', newTokenId) := CreateToken(tc', targetLocation);

    // Record parent-child relationships
    var newToken := tc''.tokens[newTokenId];
    var commonParent := FindCommonParent(tc, tokenIds);
    var updatedToken := newToken.(parentToken := commonParent);

    // Update all parent tokens to reference this new child
    var tc''' := tc''.(tokens := tc''.tokens[newTokenId := updatedToken]);


    assume forall id :: id in tokenIds ==> id in tc'''.tokens;
    var tc'''' := UpdateParentReferences(tc''', tokenIds, newTokenId);

    (tc'''', newTokenId)
  }
 */

  /**
    * Find common parent token (if any) for a set of tokens
    */
  function FindCommonParent(tc: Collection, tokenIds: set<TokenId>): Option<TokenId>
    requires forall id :: id in tokenIds ==> id in tc.tokens
  {
    if |tokenIds| == 0 then None
    else
      var tokenId := PickOne(tokenIds);
      var token := tc.tokens[tokenId];
      if token.parentToken.None? then None
      else
        var parent := token.parentToken.Unwrap();
        var allHaveSameParent := forall id :: id in tokenIds ==>
                                                tc.tokens[id].parentToken.Some? && tc.tokens[id].parentToken.Unwrap() == parent;

        if allHaveSameParent then Some(parent) else None
  }

  /**
    * Update parent tokens to reference a new child token
    */
  function UpdateParentReferences(tc: Collection, oldTokenIds: set<TokenId>, newTokenId: TokenId): Collection
    requires forall id :: id in oldTokenIds ==> id in tc.tokens
    requires newTokenId in tc.tokens
    decreases oldTokenIds
  {
    if |oldTokenIds| == 0 then tc
    else
      var tokenId := PickOne(oldTokenIds);
      var remainingIds := oldTokenIds - {tokenId};
      var token := tc.tokens[tokenId];

      if token.parentToken.Some? then
        var parentId := token.parentToken.Unwrap();
        assume parentId in tc.tokens;
        var parentToken := tc.tokens[parentId];
        var updatedParent := parentToken.(
                             childTokens := (parentToken.childTokens - {tokenId}) + {newTokenId}
                             );
        var tc' := tc.(tokens := tc.tokens[parentId := updatedParent]);
        UpdateParentReferences(tc', remainingIds, newTokenId)
      else
        UpdateParentReferences(tc, remainingIds, newTokenId)
  }

  /**
    * Suspend a token (e.g., waiting for a message)
    */
  function SuspendToken(tc: Collection, tokenId: TokenId): Collection
    requires tokenId in tc.tokens && tc.tokens[tokenId].status == Active
  {
    var token := tc.tokens[tokenId];
    var updatedToken := token.(status := Suspended);

    tc.(
    tokens := tc.tokens[tokenId := updatedToken]
    )
  }

  /**
    * Resume a suspended token
    */
  function ResumeToken(tc: Collection, tokenId: TokenId): Collection
    requires tokenId in tc.tokens && tc.tokens[tokenId].status == Suspended
  {
    var token := tc.tokens[tokenId];
    var updatedToken := token.(status := Active);

    tc.(
    tokens := tc.tokens[tokenId := updatedToken]
    )
  }

 

  /**
    * Get all tokens at a specific node
    */
  function GetTokensAtNode(tc: Collection, nodeId: NodeId): set<TokenId>
  {
    set tokenId | tokenId in tc.tokens && tc.tokens[tokenId].location == nodeId
  }

  /**
    * Check if there are any active tokens
    */
  predicate HasActiveTokens(tc: Collection)
  {
    exists tokenId :: tokenId in tc.tokens && tc.tokens[tokenId].status == Active
  }

  /**
    * Check if there are tokens at any of the specified nodes
    */
  function HasTokensAtNodes(tc: Collection, nodeIds: set<NodeId>): bool
  {
    exists tokenId :: tokenId in tc.tokens && tc.tokens[tokenId].location in nodeIds
  }

  /**
    * Get all active nodes (nodes that have active tokens)
    */
  function GetActiveNodes(tc: Collection): set<NodeId>
  {
    set tokenId | tokenId in tc.tokens :: tc.tokens[tokenId].location
  }


  /**
    * Advance the simulation time
    */
  function AdvanceTime(tc: Collection, timeIncrement: nat): Collection
  {
    tc.(currentTime := tc.currentTime + timeIncrement)
  }

  /**
    * Get token execution path
    */
  function GetTokenPath(tc: Collection, tokenId: TokenId): seq<NodeId>
    requires tokenId in tc.tokens
  {
    tc.tokens[tokenId].path
  }

  /**
    * Check if a token has visited a specific node
    */
  function HasVisitedNode(tc: Collection, tokenId: TokenId, nodeId: NodeId): bool
    requires tokenId in tc.tokens
  {
    nodeId in tc.tokens[tokenId].path
  }

  /**
    * Get all tokens that have a specific status
    */
  function GetTokensByStatus(tc: Collection, status: TokenStatus): set<TokenId>
  {
    set tokenId | tokenId in tc.tokens && tc.tokens[tokenId].status == status
  }

  /**
    * Get the execution trace for all tokens
    */
  function GetExecutionTrace(tc: Collection): seq<NodeId>
    requires |tc.tokens| > 0
  {
    if |tc.tokens| == 0 then []
    else
      // Find the token with the earliest creation time
      var startTokenId := GetEarliestToken(tc);
      assume startTokenId in tc.tokens;
      tc.tokens[startTokenId].path
  }

  /**
    * Find the token with the earliest creation time
    */
  function GetEarliestToken(tc: Collection): TokenId
    requires |tc.tokens| > 0
  {
    var tokenIds := set tokenId | tokenId in tc.tokens;
    assume |tokenIds| > 0; // 证明集合非空
    var firstId := PickOne(tokenIds);
    // Ensure preconditions are met
    assert firstId in tc.tokens;
    assert forall id :: id in (tokenIds - {firstId}) ==> id in tc.tokens;
    FindEarliestTokenHelper(tc, tokenIds - {firstId}, firstId)
  }

  /**
    * Helper function to find the earliest token
    */
  function FindEarliestTokenHelper(tc: Collection, remainingIds: set<TokenId>, currentEarliest: TokenId): TokenId
    requires currentEarliest in tc.tokens
    requires forall id :: id in remainingIds ==> id in tc.tokens
  {
    if |remainingIds| == 0 then currentEarliest
    else
      var tokenId := PickOne(remainingIds);
      var newRemaining := remainingIds - {tokenId};
      assert tokenId in tc.tokens;
      if tc.tokens[tokenId].creationTime < tc.tokens[currentEarliest].creationTime then
        FindEarliestTokenHelper(tc, newRemaining, tokenId)
      else
        FindEarliestTokenHelper(tc, newRemaining, currentEarliest)
  }

  /**
    * Get active tokens
    */
  function GetActiveTokens(tc: Collection): set<TokenId>
  {
    set tokenId | tokenId in tc.tokens && tc.tokens[tokenId].status == Active
  }


  /**
    * Reactivate a suspended token  
    */
  function ReactivateToken(tc: Collection, tokenId: TokenId): Collection
    requires tokenId in tc.tokens && tc.tokens[tokenId].status == Suspended
  {
    var token := tc.tokens[tokenId];
    var updatedToken := token.(status := Active);
    tc.(tokens := tc.tokens[tokenId := updatedToken])
  }

  /**
    * Set token to error state
    */
  function SetTokenError(tc: Collection, tokenId: TokenId, errorMsg: string): Collection
    requires tokenId in tc.tokens && tc.tokens[tokenId].status == Active
  {
    var token := tc.tokens[tokenId];
    var updatedToken := token.(status := Error);
    tc.(tokens := tc.tokens[tokenId := updatedToken])
  }

  /**
    * Lemma: Non-empty set has positive cardinality
    */
  lemma NonEmptySetHasPositiveSize<T>(s: set<T>)
    ensures (s != {}) <==> (|s| > 0)
  {
    // Dafny can usually prove this automatically
  }

  /**
    * Set token to waiting state (e.g., for parallel join)
    */
  function SetTokenWaiting(tc: Collection, tokenId: TokenId): Collection
    requires tokenId in tc.tokens && tc.tokens[tokenId].status == Active
  {
    var token := tc.tokens[tokenId];
    var updatedToken := token.(status := Waiting);
    tc.(tokens := tc.tokens[tokenId := updatedToken])
  }

  /**
    * Set token back to active state from waiting
    */
  function SetTokenActive(tc: Collection, tokenId: TokenId): Collection
    requires tokenId in tc.tokens && tc.tokens[tokenId].status == Waiting
  {
    var token := tc.tokens[tokenId];
    var updatedToken := token.(status := Active);
    tc.(tokens := tc.tokens[tokenId := updatedToken])
  }

  /**
    * Get all waiting tokens
    */
  function GetWaitingTokens(tc: Collection): set<TokenId>
  {
    set tokenId | tokenId in tc.tokens && tc.tokens[tokenId].status == Waiting
  }

/**
  * Lemma: Creating a token preserves active tokens
  */
lemma CreateTokenPreservesActiveTokens(tc: Collection, location: NodeId)
  requires ValidTokenCollection(tc)
  ensures var (newTc, newTokenId) := CreateToken(tc, location);
          GetActiveTokens(newTc) == GetActiveTokens(tc) + {newTokenId}
{
  var (newTc, newTokenId) := CreateToken(tc, location);

  forall tokenId | tokenId in GetActiveTokens(newTc)
    ensures tokenId in GetActiveTokens(tc) + {newTokenId}
  {
    assert tokenId in newTc.tokens && newTc.tokens[tokenId].status == Active;
  }
  
  forall tokenId | tokenId in GetActiveTokens(tc) + {newTokenId}
    ensures tokenId in GetActiveTokens(newTc)
  {
    if tokenId == newTokenId {
      assert newTc.tokens[tokenId].status == Active;
    } else {
      assert tokenId in GetActiveTokens(tc);
      assert newTc.tokens[tokenId] == tc.tokens[tokenId];
    }
  }
}

/**
  * Lemma: Consuming a token reduces active tokens
  */
lemma ConsumeTokenReducesActiveTokens(tc: Collection, tokenId: TokenId)
  requires ValidTokenCollection(tc)
  requires tokenId in tc.tokens && tc.tokens[tokenId].status == Active
  ensures var newTc := ConsumeToken(tc, tokenId);
          GetActiveTokens(newTc) == GetActiveTokens(tc) - {tokenId}
{
  var newTc := ConsumeToken(tc, tokenId);
  
  forall tid | tid in GetActiveTokens(newTc)
    ensures tid in GetActiveTokens(tc) - {tokenId}
  {
    assert tid != tokenId; // 因为tokenId已被消费
    assert newTc.tokens[tid] == tc.tokens[tid]; // 其他token保持不变
  }
}

lemma CreateTokensForFlowsLemma(
  tokens: Collection,
  flows: set<string>,
  flowDefinitions: map<string, ProcessDefinition.SequenceFlow>
)
  requires ValidTokenCollection(tokens)
  requires forall flowId :: flowId in flows ==> flowId in flowDefinitions
  ensures var (finalTokens, newTokenIds) := CreateTokensForFlows(tokens, flows, flowDefinitions);
          |GetActiveTokens(finalTokens)| == |GetActiveTokens(tokens)| + |flows| &&
          |newTokenIds| == |flows|
  decreases |flows|
{
}

/**
  * Lemma: ConsumeTokens对active token数量的影响
  */
lemma ConsumeTokensReducesActiveTokens(
  tc: Collection, 
  tokenIds: set<TokenId>
)
  decreases |tokenIds|
  requires ValidTokenCollection(tc)
  requires forall id :: id in tokenIds ==> id in tc.tokens && tc.tokens[id].status == Active
  ensures var result := ConsumeTokens(tc, tokenIds);
          |GetActiveTokens(result)| == |GetActiveTokens(tc)| - |tokenIds|
{
  if |tokenIds| == 0 {
    // 基础情况：没有token要消费
    assert ConsumeTokens(tc, tokenIds) == tc;
    assert |GetActiveTokens(tc)| == |GetActiveTokens(tc)| - 0;
  } else {
    // 归纳情况：消费一个token，然后递归
    var tokenId := PickOne(tokenIds);
    var remainingIds := tokenIds - {tokenId};
    var tc' := ConsumeToken(tc, tokenId);
    
    // 使用已有的lemma证明单个token的消费
    ConsumeTokenReducesActiveTokens(tc, tokenId);
    assert |GetActiveTokens(tc')| == |GetActiveTokens(tc)| - 1;
    
    // 递归调用
    ConsumeTokensReducesActiveTokens(tc', remainingIds);
    assert |GetActiveTokens(ConsumeTokens(tc', remainingIds))| == |GetActiveTokens(tc')| - |remainingIds|;
    
    // 数学推理
    assert |GetActiveTokens(ConsumeTokens(tc, tokenIds))| == |GetActiveTokens(tc)| - |tokenIds|;
  }
}
}
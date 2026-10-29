module VSharp.IL.Serializer

open System
open System.Collections.Generic
open System.IO
open System.Reflection
open System.Text.Json
open Microsoft.FSharp.Collections
open VSharp
open VSharp.GraphUtils
open VSharp.ML.GameServer.Messages
open FSharpx.Collections
open type VSharp.Core.termNode
open VSharp.Core



[<Struct>]
type Statistics =
    val CoveredVerticesInZone: uint
    val CoveredVerticesOutOfZone: uint
    val VisitedVerticesInZone: uint
    val VisitedVerticesOutOfZone: uint
    val VisitedInstructionsInZone: uint
    val TouchedVerticesInZone: uint
    val TouchedVerticesOutOfZone: uint
    val TotalVisibleVerticesInZone: uint

    new
        (
            coveredVerticesInZone,
            coveredVerticesOutOfZone,
            visitedVerticesInZone,
            visitedVerticesOutOfZone,
            visitedInstructionsInZone,
            touchedVerticesInZone,
            touchedVerticesOutOfZone,
            totalVisibleVerticesInZone
        ) =
        { CoveredVerticesInZone = coveredVerticesInZone
          CoveredVerticesOutOfZone = coveredVerticesOutOfZone
          VisitedVerticesInZone = visitedVerticesInZone
          VisitedVerticesOutOfZone = visitedVerticesOutOfZone
          VisitedInstructionsInZone = visitedInstructionsInZone
          TouchedVerticesInZone = touchedVerticesInZone
          TouchedVerticesOutOfZone = touchedVerticesOutOfZone
          TotalVisibleVerticesInZone = totalVisibleVerticesInZone }

[<Struct>]
type StateMetrics =
    val StateId: uint<stateId>
    val NextInstructionIsUncoveredInZone: float
    val ChildNumber: uint
    val VisitedVerticesInZone: uint
    val HistoryLength: uint
    val DistanceToNearestUncovered: uint
    val DistanceToNearestNotVisited: uint
    val DistanceToNearestReturn: uint

    new
        (
            stateId,
            nextInstructionIsUncoveredInZone,
            childNumber,
            visitedVerticesInZone,
            historyLength,
            distanceToNearestUncovered,
            distanceToNearestNotVisited,
            distanceTuNearestReturn
        ) =
        { StateId = stateId
          NextInstructionIsUncoveredInZone = nextInstructionIsUncoveredInZone
          ChildNumber = childNumber
          VisitedVerticesInZone = visitedVerticesInZone
          HistoryLength = historyLength
          DistanceToNearestUncovered = distanceToNearestUncovered
          DistanceToNearestNotVisited = distanceToNearestNotVisited
          DistanceToNearestReturn = distanceTuNearestReturn }

[<Struct>]
type StateInfoToDump =
    val StateId: uint<stateId>
    val NextInstructionIsUncoveredInZone: float
    val ChildNumberNormalized: float
    val VisitedVerticesInZoneNormalized: float
    val Productivity: float
    val DistanceToReturnNormalized: float
    val DistanceToUncoveredNormalized: float
    val DistanceToNotVisitedNormalized: float
    val ExpectedWeight: float

    new
        (
            stateId,
            nextInstructionIsUncoveredInZone,
            childNumber,
            visitedVerticesInZone,
            productivity,
            distanceToReturn,
            distanceToUncovered,
            distanceToNotVisited
        ) =
        { StateId = stateId
          NextInstructionIsUncoveredInZone = nextInstructionIsUncoveredInZone
          ChildNumberNormalized = childNumber
          VisitedVerticesInZoneNormalized = visitedVerticesInZone
          Productivity = productivity
          DistanceToReturnNormalized = distanceToReturn
          DistanceToUncoveredNormalized = distanceToUncovered
          DistanceToNotVisitedNormalized = distanceToNotVisited
          ExpectedWeight =
            nextInstructionIsUncoveredInZone
            + childNumber
            + visitedVerticesInZone
            + distanceToReturn
            + distanceToUncovered
            + distanceToNotVisited
            + productivity }

let mutable firstFreeEpisodeNumber = 0

let calculateStateMetrics interproceduralGraphDistanceFrom (state: IGraphTrackableState) =
    let currentBasicBlock = state.CodeLocation.BasicBlock

    let distances =
        let assembly = currentBasicBlock.Method.Module.Assembly

        let callGraphDist =
            Dict.getValueOrUpdate interproceduralGraphDistanceFrom assembly (fun () -> Dictionary<_, _>())

        Dict.getValueOrUpdate callGraphDist (currentBasicBlock :> IInterproceduralCfgNode) (fun () ->
            let dist =
                incrementalSourcedShortestDistanceBfs (currentBasicBlock :> IInterproceduralCfgNode) callGraphDist

            let distFromNode = Dictionary<IInterproceduralCfgNode, uint>()

            for i in dist do
                if i.Value <> infinity then
                    distFromNode.Add(i.Key, i.Value)

            distFromNode)

    let childCountStore = Dictionary<_, HashSet<_>>()

    let rec childCount (state: IGraphTrackableState) =
        if childCountStore.ContainsKey state then
            childCountStore[state]
        else
            let cnt =
                Array.fold
                    (fun (cnt: HashSet<_>) n ->
                        cnt.UnionWith(childCount n)
                        cnt)
                    (HashSet<_>(state.Children))
                    state.Children

            childCountStore.Add(state, cnt)
            cnt

    let childNumber = uint (childCount state).Count

    let visitedVerticesInZone =
        state.History
        |> Seq.fold
            (fun cnt kvp ->
                if kvp.Key.IsGoal && not kvp.Key.IsCovered then
                    cnt + 1u
                else
                    cnt)
            0u

    let nextInstructionIsUncoveredInZone =
        let notTouchedFollowingBlocs, notVisitedFollowingBlocs, notCoveredFollowingBlocs =
            let mutable notCoveredBasicBlocksInZone = 0
            let mutable notVisitedBasicBlocksInZone = 0
            let mutable notTouchedBasicBlocksInZone = 0
            let basicBlocks = HashSet<_>()

            currentBasicBlock.OutgoingEdges.Values |> Seq.iter basicBlocks.UnionWith

            basicBlocks
            |> Seq.iter (fun basicBlock ->
                if basicBlock.IsGoal then
                    if not basicBlock.IsTouched then
                        notTouchedBasicBlocksInZone <- notTouchedBasicBlocksInZone + 1
                    elif not basicBlock.IsVisited then
                        notVisitedBasicBlocksInZone <- notVisitedBasicBlocksInZone + 1
                    elif not basicBlock.IsCovered then
                        notCoveredBasicBlocksInZone <- notCoveredBasicBlocksInZone + 1)

            notTouchedBasicBlocksInZone, notVisitedBasicBlocksInZone, notCoveredBasicBlocksInZone

        if
            state.CodeLocation.offset <> currentBasicBlock.FinalOffset
            && currentBasicBlock.IsGoal
        then
            if not currentBasicBlock.IsVisited then 1.0
            elif not currentBasicBlock.IsCovered then 0.5
            else 0.0
        elif state.CodeLocation.offset = currentBasicBlock.FinalOffset then
            if notTouchedFollowingBlocs > 0 then 1.0
            elif notVisitedFollowingBlocs > 0 then 0.5
            elif notCoveredFollowingBlocs > 0 then 0.3
            else 0.0
        else
            0.0

    let historyLength =
        state.History |> Seq.fold (fun cnt kvp -> cnt + kvp.Value.NumOfVisits) 0u

    let getMinBy cond =
        let s = distances |> Seq.filter cond

        if Seq.isEmpty s then
            UInt32.MaxValue
        else
            s |> Seq.minBy (fun x -> x.Value) |> (fun x -> x.Value)

    let distanceToNearestUncovered =
        getMinBy (fun kvp -> kvp.Key.IsGoal && not kvp.Key.IsCovered)

    let distanceToNearestNotVisited =
        getMinBy (fun kvp -> kvp.Key.IsGoal && not kvp.Key.IsVisited)

    let distanceToNearestReturn = getMinBy (fun kvp -> kvp.Key.IsGoal && kvp.Key.IsSink)

    StateMetrics(
        state.Id,
        nextInstructionIsUncoveredInZone,
        childNumber,
        visitedVerticesInZone,
        historyLength,
        distanceToNearestUncovered,
        distanceToNearestNotVisited,
        distanceToNearestReturn
    )

let getFolderToStoreSerializationResult (prefix: string) suffix =
    let folderName = Path.Combine(Path.Combine(prefix, "SerializedEpisodes"), suffix)
    folderName

let computeStatistics (gameState: GameState) =
    let mutable coveredVerticesInZone = 0u
    let mutable coveredVerticesOutOfZone = 0u
    let mutable visitedVerticesInZone = 0u
    let mutable visitedVerticesOutOfZone = 0u
    let mutable visitedInstructionsInZone = 0u
    let mutable touchedVerticesInZone = 0u
    let mutable touchedVerticesOutOfZone = 0u
    let mutable totalVisibleVerticesInZone = 0u

    for v in gameState.GraphVertices do
        if v.CoveredByTest && v.InCoverageZone then
            coveredVerticesInZone <- coveredVerticesInZone + 1u

        if v.CoveredByTest && not v.InCoverageZone then
            coveredVerticesOutOfZone <- coveredVerticesOutOfZone + 1u

        if v.VisitedByState && v.InCoverageZone then
            visitedVerticesInZone <- visitedVerticesInZone + 1u

        if v.VisitedByState && not v.InCoverageZone then
            visitedVerticesOutOfZone <- visitedVerticesOutOfZone + 1u

        if v.InCoverageZone then
            totalVisibleVerticesInZone <- totalVisibleVerticesInZone + 1u
            visitedInstructionsInZone <- visitedInstructionsInZone + v.BasicBlockSize

        if v.TouchedByState && v.InCoverageZone then
            touchedVerticesInZone <- touchedVerticesInZone + 1u

        if v.TouchedByState && not v.InCoverageZone then
            touchedVerticesOutOfZone <- touchedVerticesOutOfZone + 1u

    Statistics(
        coveredVerticesInZone,
        coveredVerticesOutOfZone,
        visitedVerticesInZone,
        visitedVerticesOutOfZone,
        visitedInstructionsInZone,
        touchedVerticesInZone,
        touchedVerticesOutOfZone,
        totalVisibleVerticesInZone
    )

// Stable semantic key for a basic block (method identity + position within
// it); used to order blocks deterministically at serialization time.
let basicBlockKey (bb: BasicBlock) = (bb.Method.FullName, int bb.StartOffset)

let collectStatesInfoToDump (basicBlocks: ResizeArray<BasicBlock>) =
    let statesMetrics = ResizeArray<_>()

    for currentBasicBlock in
        basicBlocks |> Seq.sortBy basicBlockKey do
        let interproceduralGraphDistanceFrom =
            Dictionary<Assembly, distanceCache<IInterproceduralCfgNode>>()

        currentBasicBlock.AssociatedStates
        |> Seq.sortBy (fun (s: IGraphTrackableState) -> s.Id)
        |> Seq.iter (fun s -> statesMetrics.Add(calculateStateMetrics interproceduralGraphDistanceFrom s))

    let statesInfoToDump =
        let mutable maxVisitedVertices = UInt32.MinValue
        let mutable maxChildNumber = UInt32.MinValue
        let mutable minDistToUncovered = UInt32.MaxValue
        let mutable minDistToNotVisited = UInt32.MaxValue
        let mutable minDistToReturn = UInt32.MaxValue

        statesMetrics
        |> ResizeArray.iter (fun s ->
            if s.VisitedVerticesInZone > maxVisitedVertices then
                maxVisitedVertices <- s.VisitedVerticesInZone

            if s.ChildNumber > maxChildNumber then
                maxChildNumber <- s.ChildNumber

            if s.DistanceToNearestUncovered < minDistToUncovered then
                minDistToUncovered <- s.DistanceToNearestUncovered

            if s.DistanceToNearestNotVisited < minDistToNotVisited then
                minDistToNotVisited <- s.DistanceToNearestNotVisited

            if s.DistanceToNearestReturn < minDistToReturn then
                minDistToReturn <- s.DistanceToNearestReturn)

        let normalize minV v (sm: StateMetrics) =
            if
                v = minV
                || (v = UInt32.MaxValue && sm.DistanceToNearestReturn = UInt32.MaxValue)
            then
                1.0
            elif v = UInt32.MaxValue then
                0.0
            else
                float (1u + minV) / float (1u + v)

        statesMetrics
        |> ResizeArray.map (fun m ->
            StateInfoToDump(
                m.StateId,
                m.NextInstructionIsUncoveredInZone,
                (if maxChildNumber = 0u then
                     0.0
                 else
                     float m.ChildNumber / float maxChildNumber),
                (if maxVisitedVertices = 0u then
                     0.0
                 else
                     float m.VisitedVerticesInZone / float maxVisitedVertices),
                float m.VisitedVerticesInZone / float m.HistoryLength,
                normalize minDistToReturn m.DistanceToNearestReturn m,
                normalize minDistToUncovered m.DistanceToNearestUncovered m,
                normalize minDistToUncovered m.DistanceToNearestNotVisited m
            ))
        |> ResizeArray.sortBy (fun s -> s.StateId)

    statesInfoToDump

// Injective name for an operation (Operations.operationToString is not:
// Divide and Divide_Un both render as " / ").
let operationName (op: Core.operation) : string =
    match op with
    | Operator ot -> $"Op:{Enum.GetName(typeof<OperationType>, ot)}"
    | Application f -> $"App:{Enum.GetName(typeof<StandardFunction>, f)}"
    | Cast(src, dst) -> $"Cast:{src}->{dst}"
    | Combine -> "Combine"

// Canonical structural signature of a term: a deterministic stand-in for the
// term's structure, used to order and deduplicate path-condition vertices so
// that serialization is a pure function of the logical state.
type termSig =
    | SigAtom of string
    | SigNode of string * termSig list

// Memo is keyed by term object identity; structurally equal but distinct
// objects simply recompute the same signature. The memo is threaded per
// serialization episode (no module-level cache).
let rec termSig (memo: Dictionary<Core.term, termSig>) (t: Core.term) : termSig =
    match memo.TryGetValue t with
    | true, s -> s
    | false, _ ->
        let s =
            match t.term with
            | Nop -> SigAtom "Nop"
            | Concrete(obj, typ) -> SigNode("Concrete", [SigAtom (sprintf "%O" obj); SigAtom (string typ)])
            | Constant(name, _, typ) -> SigNode("Constant", [SigAtom name.v; SigAtom (string typ)])
            | Expression(op, terms, typ) ->
                SigNode(operationName op, List.map (termSig memo) terms @ [SigAtom (string typ)])
            | Struct(fields, typ) ->
                let fields =
                    PersistentDict.toSeq fields
                    |> List.ofSeq
                    |> List.map (fun (fid, f) -> SigNode("Field", [SigAtom (string fid); termSig memo f]))
                    |> List.sort
                SigNode("Struct", fields @ [SigAtom (string typ)])
            | HeapRef(addr, typ) -> SigNode("HeapRef", [termSig memo addr; SigAtom (string typ)])
            | Ref addr -> SigNode("Ref", [addressSig memo addr])
            | Ptr(ptrBase, typ, offset) -> SigNode("Ptr", [pointerBaseSig memo ptrBase; SigAtom (string typ); termSig memo offset])
            | Slice(t, slices) ->
                SigNode(
                    "Slice",
                    [termSig memo t]
                    @ List.map
                        (fun (s, e, p, w) -> SigNode("SliceElem", [termSig memo s; termSig memo e; termSig memo p; SigAtom (string w)]))
                        slices)
            | Ite ite ->
                SigNode(
                    "Ite",
                    List.map (fun (g, v) -> SigNode("IteBranch", [termSig memo g; termSig memo v])) ite.branches
                    @ [termSig memo ite.elseValue])
        memo.[t] <- s
        s

and addressSig (memo: Dictionary<Core.term, termSig>) (a: Core.address) : termSig =
    match a with
    | PrimitiveStackLocation key -> SigAtom $"Addr:Stack:{key}"
    | StructField(addr, field) -> SigNode("Addr:StructField", [addressSig memo addr; SigAtom (string field)])
    | StackBufferIndex(key, idx) -> SigNode("Addr:StackBufferIndex", [SigAtom (string key); termSig memo idx])
    | BoxedLocation(t, typ) -> SigNode("Addr:Boxed", [termSig memo t; SigAtom (string typ)])
    | ClassField(addr, field) -> SigNode("Addr:ClassField", [termSig memo addr; SigAtom (string field)])
    | ArrayIndex(addr, indices, typ) ->
        SigNode("Addr:ArrayIndex", [termSig memo addr] @ List.map (termSig memo) indices @ [SigAtom (string typ)])
    | ArrayLowerBound(addr, dim, typ) ->
        SigNode("Addr:ArrayLowerBound", [termSig memo addr; termSig memo dim; SigAtom (string typ)])
    | ArrayLength(addr, dim, typ) ->
        SigNode("Addr:ArrayLength", [termSig memo addr; termSig memo dim; SigAtom (string typ)])
    | StaticField(typ, field) -> SigNode("Addr:StaticField", [SigAtom (string typ); SigAtom (string field)])

and pointerBaseSig (memo: Dictionary<Core.term, termSig>) (b: Core.pointerBase) : termSig =
    match b with
    | StackLocation key -> SigAtom $"PtrBase:Stack:{key}"
    | HeapLocation(addr, typ) -> SigNode("PtrBase:Heap", [termSig memo addr; SigAtom (string typ)])
    | StaticLocation typ -> SigAtom $"PtrBase:Static:{typ}"

let getFirstFreePathConditionVertexId, resetPathConditionVertexIdCounter =
    let mutable count = 0u<pathConditionVertexId>

    fun () ->
        let res = count
        count <- count + 1u<pathConditionVertexId>
        res
    , fun () -> count <- 0u<pathConditionVertexId>

let termsWithId = Dictionary<termSig, uint<pathConditionVertexId>>()

let collectPathCondition
    (root: Core.term)
    (sigMemo: Dictionary<Core.term, termSig>)
    (termsWithId: Dictionary<termSig, uint<pathConditionVertexId>>)
    : ResizeArray<PathConditionVertex>
    = // TODO: Support other operations
    // Collect every term reachable from root, mirroring the traversal the
    // serializer has always performed (Expression operands, Struct field
    // values, Ptr offset, Slice elements; HeapRef/Ref/Ite contribute no
    // children).
    let reachable = ResizeArray<Core.term>()
    let seen = HashSet<Core.term>()
    let toVisit = Stack<Core.term> [| root |]

    while toVisit.Count > 0 do
        let t = toVisit.Pop()

        if seen.Add t then
            reachable.Add t
            match t.term with
            | Expression(_, terms, _) -> terms |> List.iter toVisit.Push
            | Struct(fields, _) -> PersistentDict.toSeq fields |> Seq.iter (fun (_, f) -> toVisit.Push f)
            | Ptr(_, _, offset) -> toVisit.Push offset
            | Slice(t, slices) ->
                toVisit.Push t

                for s, e, p, _ in slices do
                    toVisit.Push s
                    toVisit.Push e
                    toVisit.Push p
            | _ -> ()

    // Assign IDs to all not-yet-seen signatures in sorted order (two passes,
    // so that child IDs exist when the vertices are built).
    let newSigs =
        reachable
        |> Seq.map (fun t -> termSig sigMemo t)
        |> Seq.distinct
        |> List.ofSeq
        |> List.sort
        |> List.filter (fun s -> not <| termsWithId.ContainsKey s)

    for s in newSigs do
        termsWithId.[s] <- getFirstFreePathConditionVertexId ()

    let representative = Dictionary<termSig, Core.term>()

    for t in reachable do
        let s = termSig sigMemo t

        if not (representative.ContainsKey s) then
            representative.[s] <- t

    let idOf (t: Core.term) = termsWithId.[termSig sigMemo t]

    let buildVertex (id: uint<pathConditionVertexId>) (t: Core.term) =
        match t.term with
        | Nop -> PathConditionVertex(id, pathConditionVertexType.Nop, [||])
        | Concrete(_, _) -> PathConditionVertex(id, pathConditionVertexType.Constant, [||])
        | Constant(_, _, _) -> PathConditionVertex(id, pathConditionVertexType.Constant, [||])
        | Expression(operation, termList, _) ->
            let children = termList |> List.map idOf |> Array.ofList

            let vertexType =
                match operation with
                | Operator operator ->
                    match operator with
                    | OperationType.UnaryMinus -> pathConditionVertexType.UnaryMinus
                    | OperationType.BitwiseNot -> pathConditionVertexType.BitwiseNot
                    | OperationType.BitwiseAnd -> pathConditionVertexType.BitwiseAnd
                    | OperationType.BitwiseOr -> pathConditionVertexType.BitwiseOr
                    | OperationType.BitwiseXor -> pathConditionVertexType.BitwiseXor
                    | OperationType.LogicalNot -> pathConditionVertexType.LogicalNot
                    | OperationType.LogicalAnd -> pathConditionVertexType.LogicalAnd
                    | OperationType.LogicalOr -> pathConditionVertexType.LogicalOr
                    | OperationType.LogicalXor -> pathConditionVertexType.LogicalXor
                    | OperationType.Equal -> pathConditionVertexType.Equal
                    | OperationType.NotEqual -> pathConditionVertexType.NotEqual
                    | OperationType.Greater -> pathConditionVertexType.Greater
                    | OperationType.Greater_Un -> pathConditionVertexType.Greater_Un
                    | OperationType.Less -> pathConditionVertexType.Less
                    | OperationType.Less_Un -> pathConditionVertexType.Less_Un
                    | OperationType.GreaterOrEqual -> pathConditionVertexType.GreaterOrEqual
                    | OperationType.GreaterOrEqual_Un -> pathConditionVertexType.GreaterOrEqual_Un
                    | OperationType.LessOrEqual -> pathConditionVertexType.LessOrEqual
                    | OperationType.LessOrEqual_Un -> pathConditionVertexType.LessOrEqual_Un
                    | OperationType.Add -> pathConditionVertexType.Add
                    | OperationType.AddNoOvf -> pathConditionVertexType.AddNoOvf
                    | OperationType.AddNoOvf_Un -> pathConditionVertexType.AddNoOvf_Un
                    | OperationType.Subtract -> pathConditionVertexType.Subtract
                    | OperationType.SubNoOvf -> pathConditionVertexType.SubNoOvf
                    | OperationType.SubNoOvf_Un -> pathConditionVertexType.SubNoOvf_Un
                    | OperationType.Divide -> pathConditionVertexType.Divide
                    | OperationType.Divide_Un -> pathConditionVertexType.Divide_Un
                    | OperationType.Multiply -> pathConditionVertexType.Multiply
                    | OperationType.MultiplyNoOvf -> pathConditionVertexType.MultiplyNoOvf
                    | OperationType.MultiplyNoOvf_Un -> pathConditionVertexType.MultiplyNoOvf_Un
                    | OperationType.Remainder -> pathConditionVertexType.Remainder
                    | OperationType.Remainder_Un -> pathConditionVertexType.Remainder_Un
                    | OperationType.ShiftLeft -> pathConditionVertexType.ShiftLeft
                    | OperationType.ShiftRight -> pathConditionVertexType.ShiftRight
                    | OperationType.ShiftRight_Un -> pathConditionVertexType.ShiftRight_Un
                    | unexpectedOperation -> failwith $"Add {unexpectedOperation} support."
                | Application(_) -> pathConditionVertexType.StandardFunctionApplication
                | Cast(_, _) -> pathConditionVertexType.Cast
                | Combine -> pathConditionVertexType.Combine

            PathConditionVertex(id, vertexType, children)
        | Struct(fields, _) ->
            let children = PersistentDict.toSeq fields |> Seq.map (snd >> idOf) |> Seq.sort |> Array.ofSeq
            PathConditionVertex(id, pathConditionVertexType.Struct, children)
        | HeapRef(_, _) -> PathConditionVertex(id, pathConditionVertexType.HeapRef, [||])
        | Ref(_) -> PathConditionVertex(id, pathConditionVertexType.Ref, [||])
        | Ptr(_, _, offset) -> PathConditionVertex(id, pathConditionVertexType.Ptr, [| idOf offset |])
        | Slice(t, slices) ->
            let children = ResizeArray<uint<pathConditionVertexId>> [| idOf t |]

            for s, e, p, _ in slices do
                children.Add(idOf s)
                children.Add(idOf e)
                children.Add(idOf p)

            PathConditionVertex(id, pathConditionVertexType.Slice, children.ToArray())
        | Ite(_) -> PathConditionVertex(id, pathConditionVertexType.Ite, [||])

    // The ID counter is monotonic across calls, so appending in newSigs
    // order keeps the accumulated vertices in ID order.
    let pathConditionDelta = ResizeArray<PathConditionVertex>()

    for s in newSigs do
        pathConditionDelta.Add(buildVertex termsWithId.[s] representative.[s])

    pathConditionDelta

let collectGameState
    (basicBlocks: ResizeArray<BasicBlock>)
    filterStates
    (sigMemo: Dictionary<Core.term, termSig>)
    (termsWithId: Dictionary<termSig, uint<pathConditionVertexId>>)
    =
    // Every collection is iterated in a stable semantic order so that the
    // serialized result is a pure function of the logical state.
    let basicBlocks =
        basicBlocks
        |> Seq.sortBy basicBlockKey
        |> ResizeArray

    let vertices = ResizeArray<_>()
    let allStates = HashSet<_>()

    let activeStates =
        basicBlocks
        |> Seq.collect (fun basicBlock -> basicBlock.AssociatedStates)
        |> Seq.map (fun s -> s.Id)
        |> fun x -> HashSet x

    let pathConditionDelta = ResizeArray<PathConditionVertex>()

    for currentBasicBlock in basicBlocks do
        let states =
            currentBasicBlock.AssociatedStates
            |> Seq.sortBy (fun (s: IGraphTrackableState) -> s.Id)
            |> Seq.map (fun (s: IGraphTrackableState) ->
                let pathCondition = s.PathCondition |> PC.toSeq |> Seq.sortBy (termSig sigMemo)

                for term in pathCondition do
                    pathConditionDelta.AddRange(collectPathCondition term sigMemo termsWithId)

                let pathCondition =
                    pathCondition
                    |> Seq.map (fun t -> termsWithId.[termSig sigMemo t])
                    |> Seq.sort
                    |> Array.ofSeq

                State(
                    s.Id,
                    (uint <| s.CodeLocation.offset - currentBasicBlock.StartOffset + 1<byte_offset>)
                    * 1u<byte_offset>,
                    pathCondition,
                    s.VisitedAgainVertices,
                    s.VisitedNotCoveredVerticesInZone,
                    s.VisitedNotCoveredVerticesOutOfZone,
                    s.StepWhenMovedLastTime,
                    s.InstructionsVisitedInCurrentBlock,
                    s.History |> Seq.map (fun kvp -> kvp.Value) |> Array.ofSeq |> Array.sortBy (fun h -> h.GraphVertexId),
                    s.Children
                    |> Array.map (fun s -> s.Id)
                    |> Array.sort
                    |> (fun x ->
                        if filterStates then
                            Array.filter activeStates.Contains x
                        else
                            x)
                )
                |> allStates.Add
                |> ignore

                s.Id)
            |> Array.ofSeq


        GameMapVertex(
            currentBasicBlock.Id,
            currentBasicBlock.IsGoal,
            uint
            <| currentBasicBlock.FinalOffset - currentBasicBlock.StartOffset + 1<byte_offset>,
            currentBasicBlock.IsCovered,
            currentBasicBlock.IsVisited,
            currentBasicBlock.IsTouched,
            currentBasicBlock.ContainsCall,
            currentBasicBlock.ContainsThrow,
            states
        )
        |> vertices.Add

    let edges = ResizeArray<_>()

    for basicBlock in basicBlocks do
        for outgoingEdges in basicBlock.OutgoingEdges do
            for targetBasicBlock in outgoingEdges.Value do
                GameMapEdge(basicBlock.Id, targetBasicBlock.Id, GameEdgeLabel(int outgoingEdges.Key))
                |> edges.Add

    let edges = edges |> ResizeArray.toArray |> Array.sortBy (fun e -> (e.VertexFrom, e.VertexTo, e.Label.Token))

    GameState(vertices.ToArray(), allStates |> Array.ofSeq |> Array.sort, pathConditionDelta.ToArray(), edges)

let collectGameStateDelta () =
    let basicBlocks = HashSet<_>(Application.applicationGraphDelta.TouchedBasicBlocks)

    for method in Application.applicationGraphDelta.LoadedMethods do
        for basicBlock in method.BasicBlocks do
            basicBlock.IsGoal <- method.InCoverageZone
            let added = basicBlocks.Add(basicBlock)
            ()

    collectGameState (ResizeArray basicBlocks) false (Dictionary<Core.term, termSig>()) termsWithId

let dumpGameState fileForResultWithoutExtension (movedStateId: uint<stateId>) =
    let basicBlocks = ResizeArray<_>()

    for method in Application.loadedMethods do
        for basicBlock in method.Key.BasicBlocks do
            basicBlock.IsGoal <- method.Key.InCoverageZone
            basicBlocks.Add(basicBlock)

    let gameState =
        collectGameState basicBlocks true (Dictionary<Core.term, termSig>()) (Dictionary<termSig, uint<pathConditionVertexId>>())

    let statesInfoToDump = collectStatesInfoToDump basicBlocks
    let gameStateJson = JsonSerializer.Serialize gameState
    let statesInfoJson = JsonSerializer.Serialize statesInfoToDump
    File.WriteAllText(fileForResultWithoutExtension + "_gameState", gameStateJson)
    File.WriteAllText(fileForResultWithoutExtension + "_statesInfo", statesInfoJson)
    File.WriteAllText(fileForResultWithoutExtension + "_movedState", string movedStateId)

let computeReward (statisticsBeforeStep: Statistics) (statisticsAfterStep: Statistics) =
    let rewardForCoverage =
        (statisticsAfterStep.CoveredVerticesInZone
         - statisticsBeforeStep.CoveredVerticesInZone)
        * 1u<coverageReward>

    let rewardForVisitedInstructions =
        (statisticsAfterStep.VisitedInstructionsInZone
         - statisticsBeforeStep.VisitedInstructionsInZone)
        * 1u<visitedInstructionsReward>

    let maxPossibleReward =
        (statisticsBeforeStep.TotalVisibleVerticesInZone
         - statisticsBeforeStep.CoveredVerticesInZone)
        * 1u<maxPossibleReward>

    Reward(rewardForCoverage, rewardForVisitedInstructions, maxPossibleReward)

namespace VSharp.Explorer

open System.Collections.Generic
open Microsoft.ML.OnnxRuntime
open VSharp
open VSharp.IL.Serializer
open VSharp.ML.GameServer.Messages

type internal AISearcher(oracle:Oracle, aiAgentTrainingOptions: Option<AIAgentTrainingOptions>) =
    let stepsToSwitchToAI =
        match aiAgentTrainingOptions with
        | None -> 0u<step>
        | Some options -> options.stepsToSwitchToAI
        
    let stepsToPlay =
        match aiAgentTrainingOptions with
        | None -> 0u<step>
        | Some options -> options.stepsToPlay
        
    let mutable lastCollectedStatistics = Statistics()
    let mutable defaultSearcherSteps = 0u<step>
    let mutable (gameState:Option<GameState>) = None
    let mutable useDefaultSearcher = stepsToSwitchToAI > 0u<step>
    let mutable afterFirstAIPeek = false
    let mutable incorrectPredictedStateId = false
    let defaultSearcher =
        match aiAgentTrainingOptions with
        | None -> BFSSearcher() :> IForwardSearcher
        | Some options ->
            match options.defaultSearchStrategy with
            | BFSMode -> BFSSearcher() :> IForwardSearcher
            | DFSMode -> DFSSearcher() :> IForwardSearcher
            | x -> failwithf $"Unexpected default searcher {x}. DFS and BFS supported for now."  
    let mutable stepsPlayed = 0u<step>
    let isInAIMode () = (not useDefaultSearcher) && afterFirstAIPeek
    let q = ResizeArray<_>()
    let availableStates = HashSet<_>()
    let updateGameState (delta:GameState) =
            match gameState with
            | None ->
                gameState <- Some delta
            | Some s ->
                let updatedBasicBlocks = delta.GraphVertices |> Array.map (fun b -> b.Id) |> HashSet
                let updatedStates = delta.States |> Array.map (fun s -> s.Id) |> HashSet
                let vertices =
                    s.GraphVertices
                    |> Array.filter (fun v -> updatedBasicBlocks.Contains v.Id |> not)
                    |> ResizeArray<_>
                vertices.AddRange delta.GraphVertices
                let edges =
                    s.Map
                    |> Array.filter (fun e -> updatedBasicBlocks.Contains e.VertexFrom |> not)
                    |> ResizeArray<_>
                edges.AddRange delta.Map
                let activeStates = vertices |> Seq.collect (fun v -> v.States) |> HashSet
                
                let states =
                    let part1 =
                        s.States
                        |> Array.filter (fun s -> activeStates.Contains s.Id && (not <| updatedStates.Contains s.Id))
                        |> ResizeArray<_>
                    
                    part1.AddRange delta.States
                    
                    part1.ToArray()                    
                    |> Array.map (fun s -> State(s.Id
                                                 , s.Position                                                 
                                                 , s.PathConditionSize
                                                 , s.VisitedAgainVertices
                                                 , s.VisitedNotCoveredVerticesInZone
                                                 , s.VisitedNotCoveredVerticesOutOfZone
                                                 , s.StepWhenMovedLastTime
                                                 , s.InstructionsVisitedInCurrentBlock
                                                 , s.History
                                                 , s.Children |> Array.filter activeStates.Contains)
                    )
                
                gameState <- Some <| GameState (vertices.ToArray(), states, edges.ToArray())
                
                        
    let init states =
        q.AddRange states
        defaultSearcher.Init q  
        states |> Seq.iter (availableStates.Add >> ignore)
    let reset () =
        defaultSearcher.Reset()
        defaultSearcherSteps <- 0u<step>
        lastCollectedStatistics <- Statistics()
        gameState <- None
        afterFirstAIPeek <- false
        incorrectPredictedStateId <- false
        useDefaultSearcher <- stepsToSwitchToAI > 0u<step>
        q.Clear()
        availableStates.Clear()
    let update (parent, newSates) =
        if useDefaultSearcher
        then defaultSearcher.Update (parent,newSates)
        newSates |> Seq.iter (availableStates.Add >> ignore)
    let remove state =
        if useDefaultSearcher
        then defaultSearcher.Remove state
        let removed = availableStates.Remove state
        assert removed       
        for bb in state._history do bb.Key.AssociatedStates.Remove state |> ignore
        
    let pick selector =
        if useDefaultSearcher
        then
            defaultSearcherSteps <- defaultSearcherSteps + 1u<step>
            if Seq.length availableStates > 0
            then
                let gameStateDelta = collectGameStateDelta ()                
                updateGameState gameStateDelta
                let statistics = computeStatistics gameState.Value
                Application.applicationGraphDelta.Clear()
                lastCollectedStatistics <- statistics
                useDefaultSearcher <- defaultSearcherSteps < stepsToSwitchToAI
            defaultSearcher.Pick()
        elif Seq.length availableStates = 0
        then None
        elif Seq.length availableStates = 1
        then Some (Seq.head availableStates)
        else
            let gameStateDelta = collectGameStateDelta ()
            updateGameState gameStateDelta
            let statistics = computeStatistics gameState.Value
            if isInAIMode()
            then
                let reward = computeReward lastCollectedStatistics statistics
                oracle.Feedback (Feedback.MoveReward reward)
            Application.applicationGraphDelta.Clear()
            if stepsToPlay = stepsPlayed
            then None
            else
                let stateId = oracle.Predict gameState.Value
                afterFirstAIPeek <- true
                let state = availableStates |> Seq.tryFind (fun s -> s.internalId = stateId)                
                lastCollectedStatistics <- statistics
                stepsPlayed <- stepsPlayed + 1u<step>
                match state with
                | Some state ->                
                    Some state
                | None ->
                    incorrectPredictedStateId <- true
                    oracle.Feedback (Feedback.IncorrectPredictedStateId stateId)
                    None
    
    new (pathToONNX:string) =
        let numOfVertexAttributes = 7
        let numOfStateAttributes = 7
        let numOfHistoryEdgeAttributes = 2
        let createOracle (pathToONNX: string) =
            let session = new InferenceSession(pathToONNX)
            let runOptions = new RunOptions()
            let feedback (x:Feedback) = ()            
            let predict (gameState:GameState) =
                let stateIds = Dictionary<uint<stateId>,int>()
                let networkInput =
                    let verticesIds = Dictionary<uint<basicBlockGlobalId>,int>()
                    let res = Dictionary<_,_>()
                    let gameVertices =
                        let shape = [| int64 gameState.GraphVertices.Length; numOfVertexAttributes |]                    
                        let attributes = Array.zeroCreate (gameState.GraphVertices.Length * numOfVertexAttributes)
                        for i in 0..gameState.GraphVertices.Length - 1 do
                            let v = gameState.GraphVertices.[i]
                            verticesIds.Add(v.Id,i)
                            let i = i*numOfVertexAttributes
                            attributes.[i] <- if v.InCoverageZone then 1u else 0u
                            attributes.[i + 1] <- v.BasicBlockSize
                            attributes.[i + 2] <- if v.CoveredByTest then 1u else 0u
                            attributes.[i + 3] <- if v.VisitedByState then 1u else 0u
                            attributes.[i + 4] <- if v.TouchedByState then 1u else 0u
                            attributes.[i + 5] <- if v.ContainsCall then 1u else 0u
                            attributes.[i + 6] <- if v.ContainsThrow then 1u else 0u
                        OrtValue.CreateTensorValueFromMemory(attributes, shape)
                    
                    let states, numOfParentOfEdges, numOfHistoryEdges =
                        let mutable numOfParentOfEdges = 0
                        let mutable numOfHistoryEdges = 0
                        let shape = [| int64 gameState.States.Length; numOfStateAttributes |]                    
                        let attributes = Array.zeroCreate (gameState.States.Length * numOfStateAttributes)
                        for i in 0..gameState.States.Length - 1 do
                            let v = gameState.States.[i]
                            numOfHistoryEdges <- numOfHistoryEdges + v.History.Length
                            numOfParentOfEdges <- numOfParentOfEdges + v.Children.Length
                            stateIds.Add(v.Id,i)
                            let i = i*numOfStateAttributes
                            attributes.[i] <- uint v.Position
                            attributes.[i + 1] <- uint v.PathConditionSize
                            attributes.[i + 2] <- uint v.VisitedAgainVertices
                            attributes.[i + 3] <- uint v.VisitedNotCoveredVerticesInZone
                            attributes.[i + 4] <- uint v.VisitedNotCoveredVerticesOutOfZone
                            attributes.[i + 5] <- uint v.InstructionsVisitedInCurrentBlock
                            attributes.[i + 6] <- uint v.StepWhenMovedLastTime
                        OrtValue.CreateTensorValueFromMemory(attributes, shape)
                        ,numOfParentOfEdges
                        ,numOfHistoryEdges
                    
                    let vertexToVertexEdgesIndex,vertexToVertexEdgesAttributes =
                        let shapeOfIndex = [| 2L; gameState.Map.Length |]
                        let shapeOfAttributes = [| 1L; gameState.Map.Length |]
                        let index = Array.zeroCreate (2 * gameState.Map.Length)
                        let attributes = Array.zeroCreate gameState.Map.Length
                        gameState.Map
                        |> Array.iteri (
                            fun i e ->
                              index[i * 2] <- verticesIds[e.VertexFrom]
                              index[i * 2 + 1] <- verticesIds[e.VertexTo]
                              attributes[i] <- e.Label.Token
                            )
                            
                        OrtValue.CreateTensorValueFromMemory(index, shapeOfIndex)
                        , OrtValue.CreateTensorValueFromMemory(attributes, shapeOfAttributes)
                    
                    let historyEdgesIndex_vertexToState, historyEdgesAttributes, parentOfEdges =
                        let shapeOfParentOf = [| 2L; numOfParentOfEdges |]                    
                        let parentOf = Array.zeroCreate (2 * numOfParentOfEdges)
                        let shapeOfHistory = [|2L; numOfHistoryEdges|]
                        let historyIndex_vertexToState = Array.zeroCreate (2 * numOfHistoryEdges)
                        let shapeOfHistoryAttributes = [| int64 numOfHistoryEdgeAttributes; numOfHistoryEdges |]
                        let historyAttributes = Array.zeroCreate (2 * numOfHistoryEdges)
                        let mutable firstFreePositionInParentsOf = 0
                        let mutable firstFreePositionInHistoryIndex = 0
                        let mutable firstFreePositionInHistoryAttributes = 0
                        gameState.States
                        |> Array.iter (fun v ->
                                v.Children
                                |> Array.iteri (fun i s ->
                                    let i = firstFreePositionInParentsOf + 2 * i
                                    parentOf[i] <- stateIds[v.Id]
                                    parentOf[i + 1] <- stateIds[s]
                                    )
                                firstFreePositionInParentsOf <- firstFreePositionInParentsOf + 2 * v.Children.Length
                                v.History
                                |> Array.iteri (fun i s ->
                                    let j = firstFreePositionInHistoryIndex + 2 * i
                                    historyIndex_vertexToState[j] <- verticesIds[s.GraphVertexId]
                                    historyIndex_vertexToState[j + 1] <- stateIds[v.Id]
                                    let j = firstFreePositionInHistoryAttributes + numOfHistoryEdgeAttributes * i
                                    historyAttributes[j] <- s.NumOfVisits
                                    historyAttributes[j] <- uint s.StepWhenVisitedLastTime
                                    )
                                firstFreePositionInHistoryIndex <- firstFreePositionInHistoryIndex + 2 * v.History.Length
                                firstFreePositionInHistoryAttributes <- firstFreePositionInHistoryAttributes + numOfHistoryEdgeAttributes * v.History.Length
                            )
                        OrtValue.CreateTensorValueFromMemory(historyIndex_vertexToState, shapeOfHistory)
                        , OrtValue.CreateTensorValueFromMemory(historyAttributes, shapeOfHistoryAttributes)
                        , OrtValue.CreateTensorValueFromMemory(parentOf, shapeOfParentOf)
                        
                    let statePosition_stateToVertex, statePosition_vertexToState =
                        let data_stateToVertex = Array.zeroCreate (2 * gameState.States.Length)
                        let data_vertexToState = Array.zeroCreate (2 * gameState.States.Length)
                        let shape = [|2L; gameState.States.Length|]
                        let mutable firstFreePosition = 0
                        gameState.GraphVertices
                        |> Array.iter (
                            fun v ->
                                v.States
                                |> Array.iteri (fun i s ->
                                    let startPos = firstFreePosition + i * 2
                                    let s = stateIds[s]
                                    let v= verticesIds[v.Id]
                                    data_stateToVertex[startPos] <- s 
                                    data_stateToVertex[startPos + 1] <- v
                                    
                                    data_vertexToState[startPos] <- v
                                    data_vertexToState[startPos + 1] <- s
                                    )
                                firstFreePosition <- firstFreePosition + 2 * v.States.Length
                            )
                        OrtValue.CreateTensorValueFromMemory(data_stateToVertex, shape)
                        ,OrtValue.CreateTensorValueFromMemory(data_vertexToState, shape)
                             
                    res.Add ("game_vertex", gameVertices)
                    res.Add ("state_vertex", states)
                    res.Add ("game_vertex to game_vertex", vertexToVertexEdgesIndex)
                    res.Add ("game_vertex history state_vertex index", historyEdgesIndex_vertexToState)
                    res.Add ("game_vertex history state_vertex attrs", historyEdgesAttributes)
                    res.Add ("game_vertex in state_vertex", statePosition_vertexToState)
                    res.Add ("state_vertex parent_of state_vertex", parentOfEdges)
                    res
                    
                let output = session.Run(runOptions, networkInput, session.OutputNames)
                let weighedStates = output[0].GetTensorDataAsSpan<float>().ToArray()

                let id =
                    weighedStates
                    |> Array.mapi (fun i v -> i,v)
                    |> Array.maxBy snd
                    |> fst
                stateIds
                |> Seq.find (fun kvp -> kvp.Value = id)
                |> fun x -> x.Key
                
            Oracle(predict,feedback)

        AISearcher(createOracle pathToONNX, None)
        
    interface IForwardSearcher with
        override x.Init states = init states
        override x.Pick() = pick (always true)
        override x.Pick selector = pick selector
        override x.Update (parent, newStates) = update (parent, newStates)
        override x.States() = availableStates
        override x.Reset() = reset()
        override x.Remove cilState = remove cilState
        override x.StatesCount with get() = availableStates.Count

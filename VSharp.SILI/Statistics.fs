namespace VSharp.Interpreter.IL

open System
open System.IO
open System.Text
open System.Collections.Generic

open FSharpx.Collections
open VSharp
open VSharp.Core
open VSharp.Interpreter.IL
open VSharp.Utils

open CilStateOperations
open ipOperations

type pob = {loc : codeLocation; lvl : uint; pc : pathCondition}
    with
    override x.ToString() = $"loc = {x.loc}; lvl = %d{x.lvl}; pc = %s{Print.PrintPC x.pc}"

type pobStatus =
    | Unknown
    | Witnessed of cilState
    | Unreachable

// TODO: move statistics into (unique) instances of code location!
type public SILIStatistics() =
    let startIp2currentIp = Dictionary<codeLocation, Dictionary<codeLocation, uint>>()
    let totalVisited = Dictionary<codeLocation, uint>()
    let visitedWithHistory = Dictionary<codeLocation, HashSet<codeLocation>>()
    
    let totalBlocksCount = Dictionary<Method, uint>()    
    let blocksCoveredByTests = Dictionary<Method, HashSet<offset>>()
    let visitedBlocksNotCoveredByTests = Dictionary<cilState, Set<codeLocation>>()
    let visitedBlocks = Dictionary<cilState, Set<codeLocation>>()
    
    let unansweredPobs = List<pob>()
    let mutable startTime = DateTime.Now
    let internalFails = List<Exception>()
    let iies = List<cilState>()

    let mutable coveringStepsInsideZone = 0
    let mutable nonCoveringStepsInsideZone = 0
    let mutable coveringStepsOutsideZone = 0
    let mutable nonCoveringStepsOutsideZone = 0
    
    let getTotalBlocksCount (method : Method) : uint =
        Dict.getValueOrUpdate totalBlocksCount method (fun _ -> if method.HasBody then method.CFG.SortedOffsets |> Seq.length |> uint else 0u)

    let isHeadOfBasicBlock (codeLocation : codeLocation) =
        let method = codeLocation.method
        if method.HasBody then
            method.CFG.SortedOffsets.BinarySearch(codeLocation.offset) >= 0
        else false

    let printDict' placeHolder (d : Dictionary<codeLocation, uint>) sb (m : Method, locs) =
        let sb = PrettyPrinting.appendLine sb $"%s{placeHolder}Method = %s{m.FullName}: ["
        let sb = Seq.fold (fun sb (loc : codeLocation) ->
            PrettyPrinting.appendLine sb (sprintf "%s\t\t%s <- %d" placeHolder ((int loc.offset).ToString("X")) d.[loc])) sb locs
        PrettyPrinting.appendLine sb $"%s{placeHolder}]"

    let printDict placeHolder sb (d : Dictionary<codeLocation, uint>) =
        let keys = d.Keys
        let sortedKeys = keys |> Seq.sort |> Seq.groupBy (fun location -> location.method)
        Seq.fold (printDict' placeHolder d) sb sortedKeys

    let printPart (sb : StringBuilder) i (k : KeyValuePair<codeLocation, Dictionary<codeLocation, uint>>) =
        let sb = PrettyPrinting.appendLine sb $"Part %d{i}; Start from {k.Key}"
//        let sb = PrettyPrinting.appendLine sb
        printDict "\t\t" sb k.Value

    let pickTotalUnvisitedInCFG (currentLoc : codeLocation) : codeLocation option =
        let infinity = UInt32.MaxValue
        let method = currentLoc.method
        let suitable offset distance =
            let loc = { offset = offset; method = method }
            let numberOfVisit = Dict.getValueOrUpdate totalVisited loc (fun () -> 0u)
            distance <> infinity && distance <> 0u && numberOfVisit = 0u

        if method.HasBody then
            method.CFG.DistancesFrom currentLoc.offset
            |> Seq.sortBy (fun offsetDistancePair -> offsetDistancePair.Value)
            |> Seq.filter (fun offsetDistancePair -> suitable offsetDistancePair.Key offsetDistancePair.Value)
            |> Seq.tryHead
            |> Option.map (fun offsetDistancePair -> { offset = offsetDistancePair.Key; method = method })
        else None

    let pickUnvisitedWithHistoryInCFG (currentLoc : codeLocation) (history : codeLocation seq) : codeLocation option =
        let infinity = UInt32.MaxValue
        let method = currentLoc.method
        let suitable offset distance =
            let loc = { offset = offset; method = method }
            let totalHistory = Dict.getValueOrUpdate visitedWithHistory loc (fun () -> HashSet<_>())
            let validDistance = distance <> infinity && distance <> 0u
            let emptyHistory = totalHistory.Count = 0
            let nontrivialHistory = not <| totalHistory.IsSupersetOf(history)
            validDistance && (emptyHistory || nontrivialHistory)

        if method.HasBody then
            method.CFG.DistancesFrom currentLoc.offset
            |> Seq.sortBy (fun offsetDistancePair -> offsetDistancePair.Value)
            |> Seq.filter (fun offsetDistancePair -> suitable offsetDistancePair.Key offsetDistancePair.Value)
            |> Seq.tryHead
            |> Option.map (fun offsetDistancePair -> { offset = offsetDistancePair.Key; method = method })
        else None
        
    let isCoveredByTest (loc : codeLocation) =
        let offsets = ref null
        blocksCoveredByTests.TryGetValue(loc.method, offsets) && offsets.Value.Contains loc.offset

    let rememberForward (s : cilState) =
        let startLoc = ip2codeLocation s.startingIP
        let currentLoc = ip2codeLocation (currentIp s)
        let visited = history s
        match startLoc, currentLoc with
        | Some startLoc, Some currentLoc when isHeadOfBasicBlock currentLoc ->
            let mutable startRefDict = ref null
            if not <| startIp2currentIp.TryGetValue(startLoc, startRefDict) then
                startRefDict <- ref (Dictionary<codeLocation, uint>())
                startIp2currentIp.Add(startLoc, startRefDict.Value)
            let startDict = startRefDict.Value

            let mutable currentRef = ref 0u
            if not <| startDict.TryGetValue(currentLoc, currentRef) then
                currentRef <- ref 0u
                startDict.Add(currentLoc, 0u)
            startDict.[currentLoc] <- currentRef.Value + 1u

            let mutable totalRef = ref 0u
            if not <| totalVisited.TryGetValue(currentLoc, totalRef) then
                totalRef <- ref 0u
                totalVisited.Add(currentLoc, 0u)

            if totalRef.Value = 0u then
                if currentLoc.method.InCoverageZone then coveringStepsInsideZone <- coveringStepsInsideZone + 1
                else coveringStepsOutsideZone <- coveringStepsOutsideZone + 1
            elif currentLoc.method.InCoverageZone then nonCoveringStepsInsideZone <- nonCoveringStepsInsideZone + 1
            else nonCoveringStepsOutsideZone <- nonCoveringStepsOutsideZone + 1

            totalVisited.[currentLoc] <- totalRef.Value + 1u

            let mutable historyRef = ref null
            if not <| visitedWithHistory.TryGetValue(currentLoc, historyRef) then
                historyRef <- ref <| HashSet<_>()
                visitedWithHistory.Add(currentLoc, historyRef.Value)
            historyRef.Value.UnionWith visited
            
            if currentLoc.method.InCoverageZone && not <| isCoveredByTest currentLoc then                
                if not <| visitedBlocksNotCoveredByTests.ContainsKey s then
                    visitedBlocksNotCoveredByTests.[s] <- Set.empty
                visitedBlocksNotCoveredByTests.[s] <- visitedBlocksNotCoveredByTests.[s].Add currentLoc
                
            if not <| visitedBlocks.ContainsKey s then
                visitedBlocks.[s] <- Set.empty
            visitedBlocks.[s] <- visitedBlocks.[s].Add currentLoc
        | _ -> ()

    member x.IsCovered (loc : codeLocation) =
       Dict.getValueOrUpdate totalVisited loc (fun () -> 0u) > 0u
       
    member x.IsCoveredByTest (loc : codeLocation) = isCoveredByTest loc
        
    member x.UncoveredByTestsLocationsCount (s : cilState) =
        if visitedBlocksNotCoveredByTests.ContainsKey s then Some(Set.count visitedBlocksNotCoveredByTests.[s]) else None
        
    member x.MethodCoverage method =
        let totalInstructionsCount = getTotalBlocksCount method
        let methodBlocksCoveredByTest = ref null
        let coveringSteps = if blocksCoveredByTests.TryGetValue(method, methodBlocksCoveredByTest) then methodBlocksCoveredByTest.Value.Count else 0
        if totalInstructionsCount <> 0u then
            uint <| floor (double coveringSteps / double totalInstructionsCount * 100.0)
        else
            0u
        
    member x.TrackFinished (s : cilState) =
        assert(visitedBlocks.ContainsKey s)
        for loc in visitedBlocks.[s] do
            if not <| blocksCoveredByTests.ContainsKey loc.method then
                blocksCoveredByTests.[loc.method] <- HashSet()
            blocksCoveredByTests.[loc.method].Add loc.offset |> ignore
            
            if loc.method.InCoverageZone then
                for kvp in visitedBlocksNotCoveredByTests do
                    visitedBlocksNotCoveredByTests.[kvp.Key] <- kvp.Value.Remove loc
                
        visitedBlocksNotCoveredByTests.Remove s |> ignore
        visitedBlocks.Remove s |> ignore

    member x.TrackStepForward (s : cilState) = rememberForward s

    member x.TrackStepBackward (pob : pob) (cilState : cilState) =
        // TODO
        ()
        
    member x.TrackFork (parent : cilState) (children : cilState seq) =
        for child in children do
            visitedBlocks.[child] <- visitedBlocks.[parent]
            visitedBlocksNotCoveredByTests.[child] <- visitedBlocksNotCoveredByTests.[parent]

    member x.AddUnansweredPob (p : pob) = unansweredPobs.Add(p)
    member x.Clear() =
        startIp2currentIp.Clear()
        totalVisited.Clear()
        unansweredPobs.Clear()
        internalFails.Clear()
        iies.Clear()

    member x.ExplorationStarted() =
        x.Clear()
        startTime <- DateTime.Now


    member x.PickTotalUnvisitedInMethod loc = pickTotalUnvisitedInCFG loc

    member x.PickUnvisitedWithHistoryInCFG (loc, history) = pickUnvisitedWithHistoryInCFG loc history

    member x.CurrentExplorationTime with get() = DateTime.Now - startTime

    member x.IncompleteStates with get() = iies

    member x.InternalFails with get() = internalFails

    member x.PrintStatistics (writer : TextWriter) =
        let time = DateTime.Now - startTime
        writer.WriteLine("Total time: {0:00}:{1:00}:{2:00}.{3}.", time.Hours, time.Minutes, time.Seconds, time.Milliseconds)
        if internalFails.Count > 0 then
            writer.WriteLine()
            writer.WriteLine()
            writer.WriteLine("{0} error(s) occured!")
            internalFails |> Seq.iter writer.WriteLine
        if iies.Count > 0 then
            writer.WriteLine()
            writer.WriteLine()
            writer.WriteLine("{0} branch(es) with insufficient input information!", iies.Count)
            iies |> Seq.iter (fun state -> writer.WriteLine state.iie.Value.Message)

    member x.PrintDebugStatistics (writer : TextWriter) =
        x.PrintStatistics writer
        writer.WriteLine("Covering steps inside coverage zone: {0}", coveringStepsInsideZone)
        writer.WriteLine("Revisting steps inside coverage zone: {0}", nonCoveringStepsInsideZone)
        writer.WriteLine("Covering steps outside coverage zone: {0}", coveringStepsOutsideZone)
        writer.WriteLine("Revisting steps outside coverage zone: {0}", nonCoveringStepsOutsideZone)
        let topN = 5
        let topVisitedByMethods =
            totalVisited
            |> Seq.groupBy (fun kvp -> kvp.Key.method)
            |> Seq.map (snd >> Seq.maxBy (fun kvp -> kvp.Value))
            |> Seq.sortByDescending (fun kvp -> kvp.Value)
        let topVisitedByMethodsInZone = topVisitedByMethods |> Seq.filter (fun kvp -> kvp.Key.method.InCoverageZone) |> Seq.truncate topN
        let topVisitedByMethodsOutOfZone = topVisitedByMethods |> Seq.filter (fun kvp -> not kvp.Key.method.InCoverageZone) |> Seq.truncate topN
        if not <| Seq.isEmpty topVisitedByMethodsInZone then
            writer.WriteLine("Top {0} visited locations (one per method) in zone:", Seq.length topVisitedByMethodsInZone)
        for kvp in topVisitedByMethodsInZone do
            let offset = kvp.Key.offset
            let method = kvp.Key.method
            let times = kvp.Value
            writer.WriteLine("  offset {0} of {1}: {2} time{3}",
                                (int offset).ToString("X"), method.FullName, times,
                                (if times = 1u then "" else "s"))
        if not <| Seq.isEmpty topVisitedByMethodsOutOfZone then
            writer.WriteLine("Top {0} visited locations (one per method) out of zone:", Seq.length topVisitedByMethodsOutOfZone)
        for kvp in topVisitedByMethodsOutOfZone do
            let offset = kvp.Key.offset
            let method = kvp.Key.method
            let times = kvp.Value
            writer.WriteLine("  offset {0} of {1}: {2} time{3}",
                                (int offset).ToString("X"), method.FullName, times,
                                (if times = 1u then "" else "s"))

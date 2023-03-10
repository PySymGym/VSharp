﻿namespace VSharp.Interpreter.IL

open System.Diagnostics
open System.IO
open VSharp.IL
open VSharp.IL.Serializer
open VSharp.ML.GameServer.Messages

type searchMode =
    | DFSMode
    | BFSMode
    | ShortestDistanceBasedMode
    | RandomShortestDistanceBasedMode
    | ContributedCoverageMode
    | FairMode of searchMode
    | InterleavedMode of searchMode * int * searchMode * int
    | ConcolicMode of searchMode
    | GuidedMode of searchMode
    | AIMode

type coverageZone =
    | MethodZone
    | ClassZone
    | ModuleZone

type explorationMode =
    | TestCoverageMode of coverageZone * searchMode
    | StackTraceReproductionMode of StackTrace

type executionMode =
    | ConcolicMode
    | SymbolicMode

[<Struct>]
type Oracle =
    val Predict: GameState -> uint*float
    val Feedback: Feedback -> unit
    new (predict, feedback) = {Predict=predict; Feedback = feedback}

type SiliOptions = {
    explorationMode : explorationMode
    executionMode : executionMode
    outputDirectory : DirectoryInfo
    recThreshold : uint32
    timeout : int
    visualize : bool
    releaseBranches : bool
    maxBufferSize : int
    checkAttributes : bool
    stopOnCoverageAchieved : int
    oracle: Option<Oracle>
    coverageToSwitchToAI: uint
    stepsToPlay: uint
    serialize: bool
    pathToSerialize: string
}

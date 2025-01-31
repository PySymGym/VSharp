namespace VSharp.Explorer

open System.Diagnostics
open System.IO
open VSharp.ML.GameServer.Messages
open System.Net.Sockets

type searchMode =
    | DFSMode
    | BFSMode
    | ShortestDistanceBasedMode
    | RandomShortestDistanceBasedMode
    | ContributedCoverageMode
    | ExecutionTreeMode
    | FairMode of searchMode
    | InterleavedMode of searchMode * int * searchMode * int
    | AIMode

type coverageZone =
    | MethodZone
    | ClassZone
    | ModuleZone

type explorationMode =
    | TestCoverageMode of coverageZone * searchMode
    | StackTraceReproductionMode of StackTrace

type fuzzerIsolation = | Process

type FuzzerOptions =
    {
        isolation: fuzzerIsolation
        coverageZone: coverageZone
    }

[<Struct>]
type Oracle =
    val Predict: GameState -> uint<stateId>
    val Feedback: Feedback -> unit

    new(predict, feedback) =
        {
            Predict = predict
            Feedback = feedback
        }

/// <summary>
/// Options used in AI agent training.
/// </summary>
/// <param name="stepsToSwitchToAI">Number of steps of default searcher prior to switch to AI mode.</param>
/// <param name="stepsToPlay">Number of steps to play in AI mode.</param>
/// <param name="defaultSearchStrategy">Default searcher that will be used to play few initial steps.</param>
/// <param name="serializeSteps">Determine whether steps should be serialized.</param>
/// <param name="mapName">Name of map to play.</param>
/// <param name="mapName">Name of map to play.</param>


type AIBaseOptions =
    {
        defaultSearchStrategy: searchMode
        mapName: string
    }

type AIAgentTrainingOptions =
    {
        aiBaseOptions: AIBaseOptions
        stepsToSwitchToAI: uint<step>
        stepsToPlay: uint<step>
        oracle: option<Oracle>
    }

type AIAgentTrainingEachStepOptions =
    {
        aiAgentTrainingOptions: AIAgentTrainingOptions
    }


type AIAgentTrainingModelOptions =
    {
        aiAgentTrainingOptions: AIAgentTrainingOptions
        outputDirectory: string
        stream: Option<NetworkStream> // use it for sending steps
    }


type AIAgentTrainingMode =
    | SendEachStep of AIAgentTrainingEachStepOptions
    | SendModel of AIAgentTrainingModelOptions

type AIOptions =
    | Training of AIAgentTrainingMode
    | DatasetGenerator of AIBaseOptions

type SVMOptions =
    {
        explorationMode: explorationMode
        recThreshold: uint
        solverTimeout: int
        visualize: bool
        releaseBranches: bool
        maxBufferSize: int
        prettyChars: bool // If true, 33 <= char <= 126, otherwise any char
        checkAttributes: bool
        stopOnCoverageAchieved: int
        randomSeed: int
        stepsLimit: uint
        aiOptions: Option<AIOptions>
        pathToModel: Option<string>
        useGPU: Option<bool>
        optimize: Option<bool>
    }

type explorationModeOptions =
    | Fuzzing of FuzzerOptions
    | SVM of SVMOptions
    | Combined of SVMOptions * FuzzerOptions

type ExplorationOptions =
    {
        timeout: System.TimeSpan
        outputDirectory: DirectoryInfo
        explorationModeOptions: explorationModeOptions
    }

    member this.fuzzerOptions =
        match this.explorationModeOptions with
        | Fuzzing x -> x
        | Combined (_, x) -> x
        | _ -> failwith ""

    member this.svmOptions =
        match this.explorationModeOptions with
        | SVM x -> x
        | Combined (x, _) -> x
        | _ -> failwith ""

    member this.coverageZone =
        match this.explorationModeOptions with
        | SVM x ->
            match x.explorationMode with
            | TestCoverageMode (coverageZone, _) -> coverageZone
            | StackTraceReproductionMode _ -> failwith ""
        | Combined (_, x) -> x.coverageZone
        | Fuzzing x -> x.coverageZone

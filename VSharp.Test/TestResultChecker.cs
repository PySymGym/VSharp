using System.IO;
using System.Reflection;
using System.Diagnostics;
using VSharp.CoverageTool;
using VSharp.CSharpUtils;


namespace VSharp.Test;

public static class TestResultChecker
{
    private static readonly string TestRunnerPath = typeof(TestRunner.TestRunner).Assembly.Location;

    // Generated tests must terminate: a test with pathological inputs (e.g. an
    // algorithm looping over a billion-element input) would otherwise block the
    // caller forever, since nothing else bounds test execution time.
    private const int TestRunTimeoutMs = 60 * 1000;

    public static bool Check(DirectoryInfo testDir)
    {
        var info = new ProcessStartInfo
        {
            WorkingDirectory = testDir.FullName,
            FileName = DotnetExecutablePath.ExecutablePath,
            Arguments = $"{TestRunnerPath} {testDir.FullName}"
        };

        var proc = info.StartWithLogging(
            x => Logger.printLogString(Logger.Info, $"{x}"),
            x => Logger.printLogString(Logger.Error, $"{x}")
        );
        if (!proc.WaitForExit(TestRunTimeoutMs))
        {
            proc.Kill(entireProcessTree: true);
            proc.WaitForExit();
            Logger.printLogString(Logger.Error, $"TestRunner Check timed out after {TestRunTimeoutMs} ms!");
            return false;
        }

        var success = proc.IsSuccess();

        if (!success)
            Logger.printLogString(Logger.Error, "TestRunner Check failed!");

        return success;
    }

    public static bool Check(
        DirectoryInfo testDir,
        MethodInfo methodInfo,
        int expectedCoverage,
        out int actualCoverage,
        out string resultMessage)
    {
        var runnerWithArgs = $"{TestRunnerPath} {testDir.FullName}";
        var coverageTool = new PassiveCoverageTool(testDir, methodInfo);
        actualCoverage = coverageTool.RunWithCoverage(runnerWithArgs, TestRunTimeoutMs);
        resultMessage = string.Empty;

        if (expectedCoverage == actualCoverage)
        {
            return true;
        }

        resultMessage = $"Incomplete coverage! Expected {expectedCoverage}, but got {actualCoverage}";
        return false;
    }
}

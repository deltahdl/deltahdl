#include <gtest/gtest.h>

#include <filesystem>
#include <string>
#include <vector>

#include "common/types.h"
#include "driver/cli_options.h"
#include "fixture_scratch_dir.h"
#include "helpers_command_line.h"

using namespace delta;

namespace {

TEST(SeparateCompilationCommandLine, ConfigOptionNamesTheConfigToBeUsed) {
  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine({"--config", "rtlcfg"}, opts));
  EXPECT_EQ(opts.config, "rtlcfg");
}

TEST(SeparateCompilationCommandLine, ConfigLeftUnwrittenLeavesTheFieldEmpty) {
  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine({"--top", "adder", "adder.sv"}, opts));
  EXPECT_TRUE(opts.config.empty());
}

TEST(SeparateCompilationCommandLine, LoadLibNamesOnePrecompiledLibraryFile) {
  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine({"--load-lib", "rtl.dlib"}, opts));
  EXPECT_EQ(opts.precompiled_libs, std::vector<std::string>{"rtl.dlib"});
}

TEST(SeparateCompilationCommandLine, LoadLibWrittenTwiceKeepsBothInOrder) {
  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine(
      {"--load-lib", "rtl.dlib", "--load-lib", "gates.dlib"}, opts));
  EXPECT_EQ(opts.precompiled_libs,
            (std::vector<std::string>{"rtl.dlib", "gates.dlib"}));
}

TEST(SeparateCompilationCommandLine, TopWrittenTwiceKeepsBothInOrder) {
  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine({"--top", "t1", "--top", "t2"}, opts));
  EXPECT_EQ(opts.top_modules, (std::vector<std::string>{"t1", "t2"}));
}

TEST(SeparateCompilationCommandLine, LoadLibAndConfigNameSeparateThings) {
  CliOptions opts;
  EXPECT_TRUE(
      ParseCommandLine({"--load-lib", "rtl.dlib", "--config", "rtlcfg"}, opts));
  EXPECT_EQ(opts.config, "rtlcfg");
  EXPECT_EQ(opts.precompiled_libs, std::vector<std::string>{"rtl.dlib"});
}

TEST(SeparateCompilationCommandLine, PrecompileOptionsNameLibraryAndOutput) {
  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine(
      {"--precompile-into", "rtllib", "--precompile-out", "rtl.dlib"}, opts));
  EXPECT_EQ(opts.precompile_library, "rtllib");
  EXPECT_EQ(opts.precompile_output, "rtl.dlib");
}

TEST(SeparateCompilationCommandLine, PrecompileOptionsLeaveLoadLibEmpty) {
  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine(
      {"--precompile-into", "rtllib", "--precompile-out", "rtl.dlib"}, opts));
  EXPECT_TRUE(opts.precompiled_libs.empty());
  EXPECT_TRUE(opts.config.empty());
}

TEST(SeparateCompilationCommandLine, ConfigWithNoNameFollowingIsRejected) {
  CliOptions opts;
  EXPECT_FALSE(ParseCommandLine({"adder.sv", "--config"}, opts));
}

TEST(SeparateCompilationCommandLine, LoadLibWithNoFileFollowingIsRejected) {
  CliOptions opts;
  EXPECT_FALSE(ParseCommandLine({"adder.sv", "--load-lib"}, opts));
}

TEST(SeparateCompilationCommandLine,
     PrecompileIntoWithNoLibraryFollowingIsRejected) {
  CliOptions opts;
  EXPECT_FALSE(ParseCommandLine({"adder.sv", "--precompile-into"}, opts));
}

TEST(SeparateCompilationCommandLine,
     PrecompileOutWithNoFileFollowingIsRejected) {
  CliOptions opts;
  EXPECT_FALSE(ParseCommandLine({"adder.sv", "--precompile-out"}, opts));
}

TEST(SeparateCompilationCommandLine, UnrecognizedOptionSetsNoRejectedArgument) {
  CliOptions opts;
  EXPECT_FALSE(ParseCommandLine({"--load-library", "rtl.dlib"}, opts));
  EXPECT_FALSE(opts.rejected_argument);
}

TEST(SeparateCompilationCommandLine, SourceFileNameReachesTheSourceFiles) {
  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine({"adder.sv", "--config", "rtlcfg"}, opts));
  EXPECT_EQ(opts.source_files, std::vector<std::string>{"adder.sv"});
}

TEST(SeparateCompilationCommandLine, SeedWithTextForItsValueIsRejected) {
  CliOptions opts;
  EXPECT_FALSE(ParseCommandLine({"--seed", "random"}, opts));
  EXPECT_TRUE(opts.rejected_argument);
}

TEST(SeparateCompilationCommandLine,
     MaxGenerateIterationsWithTextForItsValueIsRejected) {
  CliOptions opts;
  EXPECT_FALSE(ParseCommandLine({"--max-generate-iterations", "many"}, opts));
  EXPECT_TRUE(opts.rejected_argument);
}

TEST(SeparateCompilationCommandLine, SeedAboveTheFieldsRangeIsRejected) {
  CliOptions opts;
  EXPECT_FALSE(ParseCommandLine({"--seed", "4294967296"}, opts));
  EXPECT_TRUE(opts.rejected_argument);
  EXPECT_EQ(opts.seed, 0U);
}

TEST(SeparateCompilationCommandLine, SeedReachesTheSeedField) {
  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine({"--seed", "7"}, opts));
  EXPECT_EQ(opts.seed, 7U);
}

TEST(SeparateCompilationCommandLine, MaxGenerateIterationsReachesItsField) {
  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine({"--max-generate-iterations", "5000"}, opts));
  EXPECT_EQ(opts.max_generate_iterations, 5000);
}

TEST(SeparateCompilationCommandLine,
     ConfigWithNoNameFollowingSetsRejectedArgument) {
  CliOptions opts;
  EXPECT_FALSE(ParseCommandLine({"adder.sv", "--config"}, opts));
  EXPECT_TRUE(opts.rejected_argument);
}

TEST(SeparateCompilationCommandLine,
     MinTypMaxWithNoValueFollowingSetsRejectedArgument) {
  CliOptions opts;
  EXPECT_FALSE(ParseCommandLine({"adder.sv", "--mintypmax"}, opts));
  EXPECT_TRUE(opts.rejected_argument);
}

TEST(SeparateCompilationCommandLine,
     MinTypMaxWithAValueOutsideTheThreeIsRejected) {
  CliOptions opts;
  EXPECT_FALSE(ParseCommandLine({"--mintypmax", "nominal"}, opts));
  EXPECT_TRUE(opts.rejected_argument);
  EXPECT_EQ(opts.mintypmax, DelayMode::kTyp);
}

TEST(SeparateCompilationCommandLine, OptionsFileCarriesAnOptionToItsField) {
  ScratchDir tmp;
  const std::string kOptionsFile =
      tmp.Write("args.f", "--top adder\n").string();

  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine({"-f", kOptionsFile}, opts));
  EXPECT_EQ(opts.top_modules, std::vector<std::string>{"adder"});
}

TEST(SeparateCompilationCommandLine,
     OptionsFileNamingItselfIsRefusedRatherThanRecursed) {
  ScratchDir tmp;
  const std::string kSelfNaming = (tmp.dir / "self.f").string();
  tmp.Write("self.f", "-f " + kSelfNaming + "\n");

  CliOptions opts;
  EXPECT_FALSE(ParseCommandLine({"-f", kSelfNaming}, opts));
}

TEST(SeparateCompilationCommandLine,
     OptionsFileOptionWithNoFileFollowingSetsRejectedArgument) {
  CliOptions opts;
  EXPECT_FALSE(ParseCommandLine({"adder.sv", "-f"}, opts));
  EXPECT_TRUE(opts.rejected_argument);
}

std::string ParseCapturingStderr(const std::vector<std::string>& args,
                                 CliOptions& opts) {
  std::string err;
  ParseCommandLineCapturingStderr(args, opts, err);
  return err;
}

TEST(SeparateCompilationCommandLine, OptionsFileNamesItselfInAMissingValue) {
  ScratchDir tmp;
  const std::string kOptionsFile =
      tmp.Write("args.f", "--top adder\n--top\n").string();

  CliOptions opts;
  std::string out = ParseCapturingStderr({"-f", kOptionsFile}, opts);
  EXPECT_NE(out.find(kOptionsFile + ":2: --top expects a value"),
            std::string::npos)
      << out;
}

TEST(SeparateCompilationCommandLine, OptionsFileNamesItselfInAnUnknownOption) {
  ScratchDir tmp;
  const std::string kOptionsFile =
      tmp.Write("args.f", "--top adder\n--tpo x\n").string();

  CliOptions opts;
  std::string out = ParseCapturingStderr({"-f", kOptionsFile}, opts);
  EXPECT_NE(out.find(kOptionsFile + ":2: unknown option: --tpo"),
            std::string::npos)
      << out;
}

TEST(SeparateCompilationCommandLine, NestedOptionsFileNamesTheInnerFile) {
  ScratchDir tmp;
  const std::string kInner = tmp.Write("inner.f", "--tpo x\n").string();
  const std::string kOuter =
      tmp.Write("outer.f", "--top adder\n-f " + kInner + "\n").string();

  CliOptions opts;
  std::string out = ParseCapturingStderr({"-f", kOuter}, opts);
  EXPECT_NE(out.find(kInner + ":1: unknown option: --tpo"), std::string::npos)
      << out;
  EXPECT_EQ(out.find(kOuter + ":"), std::string::npos) << out;
}

TEST(SeparateCompilationCommandLine, CommandLineOptionNamesNoFile) {
  CliOptions opts;
  std::string out = ParseCapturingStderr({"--tpo"}, opts);
  EXPECT_NE(out.find("unknown option: --tpo"), std::string::npos) << out;
  EXPECT_EQ(out.find(":1: "), std::string::npos) << out;
}

}  // namespace

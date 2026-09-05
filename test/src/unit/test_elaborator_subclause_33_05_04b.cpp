// §33.5.4's separate compilation options as the command line carries them:
// which option names the config, which names an already compiled library, and
// which two say where this invocation's compiled cells are written.
//
// Every case here calls ParseArgs (driver/cli_options.h) with a command line
// and reads the CliOptions field the option is supposed to reach. No case
// elaborates a design, which is what separates this file from
// test_elaborator_subclause_33_05_04a.cpp beside it: every case there compiles
// source descriptions and elaborates them, and none reads a command line.
//
// §33.5.4 is what gives these options meaning: "the tool that actually does
// the binding only needs to be given the lib.cell specification for the
// top-level cell(s) and/or the config to be used. In this strategy, the config
// itself shall also be precompiled." --config names that config and --load-lib
// names the compiled form the binding tool reads, which §33.5.3 requires to
// have persisted: "it is essential that library cells persist, and the
// compiled forms shall, therefore, exist somewhere in the filesystem".
// --precompile-into and --precompile-out are the other end of the same flow,
// naming the library this invocation's cells go into and the file they are
// written to.
//
// A rejection here is asserted through ParseArgs's return value, which is the
// whole of what ParseArgs answers about an unrecognized option.
// .claude/CLAUDE.md otherwise has a test naming the report through
// ReportedError; that applies to a rule the program reports through
// common/diagnostic.h, and ParseArgs writes to std::cerr and returns a bool
// instead. A rejection an option made itself is asserted through
// CliOptions::rejected_argument as well, which ParseArgs sets for an option it
// recognized and whose value it refused.
//
// Issue #3425 is why this half exists. CliOptions and ParseArgs were in
// src/main.cpp's anonymous namespace, where no test could name them, so an
// option renamed, dropped or wired to the wrong field left every test passing.
//
// Issue #3426 is why the cases over a malformed command line are here. A
// numeric option read its value with std::stoull, std::stoul or std::stoll,
// which throw for text that is not a number and for a number too large;
// nothing caught the exception, so a mistyped number terminated the process
// and no case could report at all. An option written last with its value left
// off reached ParseArgs's "unknown option" branch, which told the reader an
// option that exists does not. A -f options file naming itself was read again
// every time it was read, without bound. Each of the three has a case below,
// and each is paired with a case giving the same option something it accepts,
// so a parser that refused every value would fail the pair.

#include <gtest/gtest.h>

#include <filesystem>
#include <string>
#include <vector>

#include "driver/cli_options.h"
#include "fixture_scratch_dir.h"

using namespace delta;

namespace {

// Runs ParseArgs over `args`, which holds the arguments as written on the
// command line. ParseArgs starts at index 1 because argv[0] is the program
// name, so the program name is prepended here and no case writes it. The words
// are copied into buffers this function owns because ParseArgs takes a
// non-const `char* argv[]`.
bool ParseCommandLine(const std::vector<std::string>& args, CliOptions& opts) {
  std::vector<std::string> words;
  words.reserve(args.size() + 1);
  words.emplace_back("deltahdl");
  for (const std::string& arg : args) {
    words.push_back(arg);
  }
  std::vector<char*> argv;
  argv.reserve(words.size());
  for (std::string& word : words) {
    argv.push_back(word.data());
  }
  return ParseArgs(static_cast<int>(argv.size()), argv.data(), opts);
}

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

TEST(SeparateCompilationCommandLine, MaxTimeWithTextForItsValueIsRejected) {
  // std::from_chars answers that the text was not a number. std::stoull threw
  // std::invalid_argument for it and nothing caught the exception, so before
  // issue #3426 was fixed the process terminated here and no case could report
  // at all.
  CliOptions opts;
  EXPECT_FALSE(ParseCommandLine({"--max-time", "later"}, opts));
  EXPECT_TRUE(opts.rejected_argument);
}

TEST(SeparateCompilationCommandLine, SeedWithTextForItsValueIsRejected) {
  // --seed is a separate call to TakeNumber in src/driver/cli_options.cpp, so
  // it is a separate case from --max-time above.
  CliOptions opts;
  EXPECT_FALSE(ParseCommandLine({"--seed", "random"}, opts));
  EXPECT_TRUE(opts.rejected_argument);
}

TEST(SeparateCompilationCommandLine,
     MaxGenerateIterationsWithTextForItsValueIsRejected) {
  // The third of the four calls to TakeNumber, and the only one whose field is
  // signed.
  CliOptions opts;
  EXPECT_FALSE(ParseCommandLine({"--max-generate-iterations", "many"}, opts));
  EXPECT_TRUE(opts.rejected_argument);
}

TEST(SeparateCompilationCommandLine, LutSizeWithTextForItsValueIsRejected) {
  // The fourth call to TakeNumber, made from TryParseSynthArg rather than from
  // TryParseSimNumericArg.
  CliOptions opts;
  EXPECT_FALSE(ParseCommandLine({"--lut-size", "wide"}, opts));
  EXPECT_TRUE(opts.rejected_argument);
}

TEST(SeparateCompilationCommandLine, MaxTimeAboveTheFieldsRangeIsRejected) {
  // A value too large for CliOptions::max_time is
  // std::errc::result_out_of_range, which std::from_chars reports separately
  // from text that is no number at all. std::stoull threw std::out_of_range
  // for it, which is a second way the same call terminated the process.
  CliOptions opts;
  EXPECT_FALSE(
      ParseCommandLine({"--max-time", "99999999999999999999999999"}, opts));
  EXPECT_TRUE(opts.rejected_argument);
}

TEST(SeparateCompilationCommandLine,
     MaxTimeWithTrailingTextAfterItsDigitsIsRejected) {
  // std::from_chars stops at the first character it cannot read, so "100ns"
  // would set max_time to 100 unless the whole value has to be consumed for
  // the option to have been given a number.
  CliOptions opts;
  EXPECT_FALSE(ParseCommandLine({"--max-time", "100ns"}, opts));
  EXPECT_TRUE(opts.rejected_argument);
}

TEST(SeparateCompilationCommandLine, MaxTimeReachesTheMaxTimeField) {
  // 4200 is not the field's default of 0, so a parser that never read the
  // value would fail this. The four cases refusing a numeric value above would
  // all pass against a parser that refused every value; these four are what
  // rule that parser out.
  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine({"--max-time", "4200"}, opts));
  EXPECT_EQ(opts.max_time, 4200U);
}

TEST(SeparateCompilationCommandLine, SeedReachesTheSeedField) {
  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine({"--seed", "7"}, opts));
  EXPECT_EQ(opts.seed, 7U);
}

TEST(SeparateCompilationCommandLine, MaxGenerateIterationsReachesItsField) {
  // 5000 is not kDefaultMaxGenerateIterations, which
  // src/elaborator/elaborator_data.h sets to 262144.
  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine({"--max-generate-iterations", "5000"}, opts));
  EXPECT_EQ(opts.max_generate_iterations, 5000);
}

TEST(SeparateCompilationCommandLine, LutSizeReachesTheLutSizeField) {
  // 6 is not the field's default of 4.
  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine({"--lut-size", "6"}, opts));
  EXPECT_EQ(opts.lut_size, 6U);
}

TEST(SeparateCompilationCommandLine,
     ConfigWithNoNameFollowingSetsRejectedArgument) {
  // --config was recognized and its value was missing, which ParseArgs marks
  // by setting CliOptions::rejected_argument.
  // UnrecognizedOptionSetsNoRejectedArgument above is the other half of the
  // pair: the field stays false for an option that does not exist. Neither
  // case alone says what the field means, and before issue #3426 was fixed an
  // option written last with its value left off was reported as an option that
  // does not exist.
  CliOptions opts;
  EXPECT_FALSE(ParseCommandLine({"adder.sv", "--config"}, opts));
  EXPECT_TRUE(opts.rejected_argument);
}

TEST(SeparateCompilationCommandLine,
     MinTypMaxWithNoValueFollowingSetsRejectedArgument) {
  // --mintypmax answers its own missing value in TryParseMinTypMaxArg
  // (src/driver/cli_options.cpp) rather than in the TakeValue the other
  // options share, so it is a separate case from --config above.
  CliOptions opts;
  EXPECT_FALSE(ParseCommandLine({"adder.sv", "--mintypmax"}, opts));
  EXPECT_TRUE(opts.rejected_argument);
}

TEST(SeparateCompilationCommandLine,
     MinTypMaxWithAValueOutsideTheThreeIsRejected) {
  // §11.11 gives a min:typ:max expression three values and no fourth, so
  // "nominal" names none of them.
  CliOptions opts;
  EXPECT_FALSE(ParseCommandLine({"--mintypmax", "nominal"}, opts));
  EXPECT_TRUE(opts.rejected_argument);
  EXPECT_EQ(opts.mintypmax, DelayMode::kTyp);
}

TEST(SeparateCompilationCommandLine, OptionsFileCarriesAnOptionToItsField) {
  // -f names a file of further options, which ParseArgs reads in place. This
  // case is what makes OptionsFileNamingItselfIsRefusedRatherThanRecursed
  // below mean something, because a parser that refused every -f would pass
  // that case.
  ScratchDir tmp;
  const std::string kOptionsFile =
      tmp.Write("args.f", "--top adder\n").string();

  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine({"-f", kOptionsFile}, opts));
  EXPECT_EQ(opts.top_module, "adder");
}

TEST(SeparateCompilationCommandLine,
     OptionsFileNamingItselfIsRefusedRatherThanRecursed) {
  // ReadOptionsFile in src/driver/cli_options.cpp refuses past
  // kMaxOptionsFileDepth. Without that limit this command line reads the same
  // file again every time it reads it, which is what issue #3426 reports.
  ScratchDir tmp;
  const std::string kSelfNaming = (tmp.dir / "self.f").string();
  tmp.Write("self.f", "-f " + kSelfNaming + "\n");

  CliOptions opts;
  EXPECT_FALSE(ParseCommandLine({"-f", kSelfNaming}, opts));
}

TEST(SeparateCompilationCommandLine,
     OptionsFileOptionWithNoFileFollowingSetsRejectedArgument) {
  // -f is recognized and its file is missing, so it is refused the way an
  // option missing its value is rather than reported as an option that does
  // not exist.
  CliOptions opts;
  EXPECT_FALSE(ParseCommandLine({"adder.sv", "-f"}, opts));
  EXPECT_TRUE(opts.rejected_argument);
}

}  // namespace

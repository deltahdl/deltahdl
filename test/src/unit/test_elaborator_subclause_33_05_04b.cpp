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
// whole of what ParseArgs answers about an unrecognized option. CLAUDE.md
// otherwise has a test naming the report through ReportedError; that applies
// to a rule the program reports through common/diagnostic.h, and ParseArgs
// writes to std::cerr and returns a bool instead.
//
// Issue #3425 is why this half exists. CliOptions and ParseArgs were in
// src/main.cpp's anonymous namespace, where no test could name them, so an
// option renamed, dropped or wired to the wrong field left every test passing.

#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "driver/cli_options.h"

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

}  // namespace

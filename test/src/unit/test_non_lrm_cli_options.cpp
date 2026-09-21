// Tests for the driver options that choose how far deltahdl runs a source.
// These options are the program's, not the standard's: IEEE 1800-2023 names
// no command line, so no subclause is cited. Each case reads one command line
// through ParseArgs (driver/cli_options.h) and reads back the CliOptions field
// the option is supposed to reach, the way test_elaborator_subclause_33_05_04b
// does for the separate-compilation options.
//
// --parse-only is #4360's: --lint-only stops after elaboration since #4351,
// and before this no option stopped after the parse.

#include <gtest/gtest.h>

#include "driver/cli_options.h"
#include "helpers_command_line.h"

using namespace delta;

namespace {

// --parse-only reaches CliOptions::parse_only.
TEST(RunStageOptions, ParseOnlySetsParseOnly) {
  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine({"--parse-only"}, opts));
  EXPECT_TRUE(opts.parse_only);
  EXPECT_FALSE(opts.lint_only);
}

// --lint-only is a different option, reaching a different field; the two are
// not aliases.
TEST(RunStageOptions, LintOnlySetsLintOnlyAlone) {
  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine({"--lint-only"}, opts));
  EXPECT_TRUE(opts.lint_only);
  EXPECT_FALSE(opts.parse_only);
}

// Neither option written leaves both unset, which is the run to a simulation.
TEST(RunStageOptions, NoStageOptionLeavesBothUnset) {
  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine({"--top", "m", "m.sv"}, opts));
  EXPECT_FALSE(opts.parse_only);
  EXPECT_FALSE(opts.lint_only);
}

}  // namespace

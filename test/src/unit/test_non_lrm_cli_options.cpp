// Tests for the driver options IEEE 1800-2023 names no clause for: the stage a
// run stops at, the options carrying a name or a number, the flags, -D, and
// the -f options file. These options are the program's, not the standard's, so
// no subclause is cited. Each case reads one command line through ParseArgs
// (driver/cli_options.h) and reads back the CliOptions field the option is
// supposed to reach, the way test_elaborator_subclause_33_05_04b does for the
// separate-compilation options.
//
// --parse-only is #4360's: --lint-only stops after elaboration since #4351,
// and before this no option stopped after the parse.
//
// A rejection here is asserted through ParseArgs's return value and
// CliOptions::rejected_argument, with the text ParseArgs prints to std::cerr
// where the report is what the case is about: ParseArgs reports through
// neither common/diagnostic.h nor a Subclause, so ReportedError does not apply.

#include <gtest/gtest.h>

#include <iostream>
#include <sstream>
#include <streambuf>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/types.h"
#include "driver/cli_options.h"
#include "elaborator/elaborator_data.h"
#include "fixture_scratch_dir.h"
#include "helpers_command_line.h"

using namespace delta;

namespace {

// Runs one command line with std::cerr captured, answering whether the parse
// was accepted and filling `err` with what was printed.
bool ParseCapturingStderr(const std::vector<std::string>& args,
                          CliOptions& opts, std::string& err) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cerr.rdbuf(captured.rdbuf());
  bool ok = ParseCommandLine(args, opts);
  std::cerr.rdbuf(old_buf);
  err = captured.str();
  return ok;
}

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

// TakeNumber in src/driver/cli_options.cpp is a template, instantiated once
// per field type: uint32_t for --seed and int64_t for
// --max-generate-iterations. Each instantiation is separate code, so each
// refusal below is written once per type.

// A numeric option written last has no value, which is reported as missing
// rather than as an option that does not exist.
TEST(NumericOptions, NumberWrittenLastIsReportedAsMissingItsValue) {
  for (const char* name : {"--seed", "--max-generate-iterations"}) {
    CliOptions opts;
    std::string err;
    EXPECT_FALSE(ParseCapturingStderr({"m.sv", name}, opts, err)) << name;
    EXPECT_TRUE(opts.rejected_argument) << name;
    EXPECT_NE(err.find(std::string(name) + " expects a value"),
              std::string::npos)
        << err;
    EXPECT_EQ(err.find("unknown option"), std::string::npos) << err;
  }
}

// Every numeric option is a count, so a value below zero is refused before
// the digits are read. The int64_t instantiation is the one where
// std::from_chars would otherwise take -1 without complaint.
TEST(NumericOptions, NegativeNumberIsRefused) {
  for (const char* name : {"--seed", "--max-generate-iterations"}) {
    CliOptions opts;
    std::string err;
    EXPECT_FALSE(ParseCapturingStderr({name, "-1"}, opts, err)) << name;
    EXPECT_TRUE(opts.rejected_argument) << name;
    EXPECT_NE(err.find(std::string(name) +
                       " expects a number that is not negative: -1"),
              std::string::npos)
        << err;
  }
  CliOptions opts;
  EXPECT_FALSE(ParseCommandLine({"--max-generate-iterations", "-1"}, opts));
  EXPECT_EQ(opts.max_generate_iterations, kDefaultMaxGenerateIterations);
}

// std::from_chars stops at the first character that is not a digit, so a
// value with text after its digits would be read up to that character unless
// the whole of it has to be consumed.
TEST(NumericOptions, TrailingTextAfterTheDigitsIsRefused) {
  CliOptions seed_opts;
  EXPECT_FALSE(ParseCommandLine({"--seed", "7x"}, seed_opts));
  EXPECT_TRUE(seed_opts.rejected_argument);
  EXPECT_EQ(seed_opts.seed, 0U);

  CliOptions iter_opts;
  EXPECT_FALSE(
      ParseCommandLine({"--max-generate-iterations", "10k"}, iter_opts));
  EXPECT_TRUE(iter_opts.rejected_argument);
  EXPECT_EQ(iter_opts.max_generate_iterations, kDefaultMaxGenerateIterations);
}

// typ is --mintypmax's default, so it is written after min: a parser that
// ignored typ would leave min in place.
TEST(MinTypMaxOption, TypWrittenAfterMinSelectsTyp) {
  CliOptions opts;
  EXPECT_TRUE(
      ParseCommandLine({"--mintypmax", "min", "--mintypmax", "typ"}, opts));
  EXPECT_EQ(opts.mintypmax, DelayMode::kTyp);
  EXPECT_FALSE(opts.rejected_argument);
}

// Each option whose value is a name reaches its own field. The value is the
// option's own spelling, so a value landing in another option's field is seen
// there as well as missing from its own.
TEST(ValueOptions, EachNameReachesItsOwnField) {
  const std::pair<const char*, std::string CliOptions::*> kOptions[] = {
      {"--vcd", &CliOptions::vcd_file},
      {"--top", &CliOptions::top_module},
      {"--config", &CliOptions::config}};
  for (const auto& [name, field] : kOptions) {
    CliOptions opts;
    EXPECT_TRUE(ParseCommandLine({name, name}, opts)) << name;
    for (const auto& [other, other_field] : kOptions) {
      EXPECT_EQ(opts.*other_field, std::string_view(other) == name ? name : "")
          << name << " as seen in " << other;
    }
  }
}

// These options were accepted and listed in --help while nothing read what
// they set: an output name, a timescale override, FST dumping, a simulation
// time limit, Verilog library files and directories, -Wall, and the
// synthesizer's target, LUT size, Liberty library, output format, area and
// delay modes and retiming. Each is now an option deltahdl does not have, so
// the parse refuses it as it refuses any unknown option, rather than going on
// as if it had taken effect.
TEST(RemovedOptions, EachIsReportedAsAnUnknownOption) {
  for (const char* name : {"-o", "--timescale", "--fst", "--max-time", "-v",
                           "-y", "-Wall", "--target", "--lut-size", "--lib",
                           "--format", "--area", "--delay", "--retime"}) {
    CliOptions opts;
    std::string err;
    EXPECT_FALSE(ParseCapturingStderr({name}, opts, err)) << name;
    EXPECT_FALSE(opts.rejected_argument) << name;
    EXPECT_NE(err.find(std::string("unknown option: ") + name),
              std::string::npos)
        << err;
  }
}

// Each flag sets its own field and no other, so a flag wired to its
// neighbour's field fails twice: once for the field it left unset and once
// for the one it set.
TEST(FlagOptions, EachFlagSetsItsOwnFieldAlone) {
  const std::pair<const char*, bool CliOptions::*> kFlags[] = {
      {"--version", &CliOptions::show_version},
      {"--help", &CliOptions::show_help},
      {"--synth", &CliOptions::synth_mode},
      {"--lint-only", &CliOptions::lint_only},
      {"--parse-only", &CliOptions::parse_only},
      {"--dump-ast", &CliOptions::dump_ast},
      {"--dump-ir", &CliOptions::dump_ir},
      {"-Werror", &CliOptions::werror},
      {"--negative-timing-checks", &CliOptions::negative_timing_checks},
      {"--no-timing-checks", &CliOptions::no_timing_checks},
      {"--dump-aig", &CliOptions::dump_aig},
      {"--no-opt", &CliOptions::no_opt}};
  for (const auto& [name, field] : kFlags) {
    CliOptions opts;
    EXPECT_TRUE(ParseCommandLine({name}, opts)) << name;
    for (const auto& [other, other_field] : kFlags) {
      EXPECT_EQ(opts.*other_field, std::string_view(other) == name)
          << name << " as seen in " << other;
    }
  }
}

// -D takes its definition either joined to it or as the next word, and
// either way it reaches the same list.
TEST(DefineOption, JoinedAndSeparateDefinitionsBothReachTheDefines) {
  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine({"-DWIDTH=8", "-D", "FAST"}, opts));
  EXPECT_EQ(opts.defines, (std::vector<std::pair<std::string, std::string>>{
                              {"WIDTH", "8"}, {"FAST", "1"}}));
}

TEST(DefineOption, DefineWrittenLastIsReportedAsMissingItsValue) {
  CliOptions opts;
  std::string err;
  EXPECT_FALSE(ParseCapturingStderr({"m.sv", "-D"}, opts, err));
  EXPECT_TRUE(opts.rejected_argument);
  EXPECT_NE(err.find("-D expects a value"), std::string::npos) << err;
  EXPECT_TRUE(opts.defines.empty());
}

// TryParseProtectArg records a refused value on the ProtectCliOptions it is
// handed, and ParseArgs carries it to CliOptions::rejected_argument; without
// that the refused key would be reported and the run would still go on.
TEST(ProtectOptions, RefusedNamedKeyFailsTheParse) {
  CliOptions opts;
  std::string err;
  EXPECT_FALSE(
      ParseCapturingStderr({"--protect-named-key", "acme"}, opts, err));
  EXPECT_TRUE(opts.protect.rejected_argument);
  EXPECT_TRUE(opts.rejected_argument);
  EXPECT_NE(err.find("--protect-named-key expects <owner>:<name>=<key>: acme"),
            std::string::npos)
      << err;

  CliOptions accepted;
  EXPECT_TRUE(ParseCommandLine({"--protect-named-key", "acme:k=s3"}, accepted));
  EXPECT_FALSE(accepted.rejected_argument);
}

// An options file that cannot be read stops the parse there, with the path in
// the report.
TEST(OptionsFile, FileThatCannotBeOpenedStopsTheParse) {
  ScratchDir tmp;
  const std::string kAbsent = (tmp.dir / "absent.f").string();

  CliOptions opts;
  std::string err;
  EXPECT_FALSE(ParseCapturingStderr({"-f", kAbsent, "m.sv"}, opts, err));
  EXPECT_NE(err.find("cannot open options file '" + kAbsent + "'"),
            std::string::npos)
      << err;
  EXPECT_TRUE(opts.source_files.empty());
}

// A word beginning with # comments out the rest of its line and nothing
// more: the option after it on the same line is not read, and the next line
// is. A # inside a word begins no comment.
TEST(OptionsFile, HashWordCommentsOutTheRestOfItsLine) {
  ScratchDir tmp;
  const std::string kOptionsFile =
      tmp.Write("args.f", "--top adder #--seed 9\n--seed 7 a#b.sv\n").string();

  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine({"-f", kOptionsFile}, opts));
  EXPECT_EQ(opts.top_module, "adder");
  EXPECT_EQ(opts.seed, 7U);
  EXPECT_EQ(opts.source_files, std::vector<std::string>{"a#b.sv"});
}

}  // namespace

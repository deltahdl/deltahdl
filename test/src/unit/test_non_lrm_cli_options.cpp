#include <gtest/gtest.h>

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

TEST(RunStageOptions, ParseOnlySetsParseOnly) {
  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine({"--parse-only"}, opts));
  EXPECT_TRUE(opts.parse_only);
  EXPECT_FALSE(opts.lint_only);
}

TEST(RunStageOptions, LintOnlySetsLintOnlyAlone) {
  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine({"--lint-only"}, opts));
  EXPECT_TRUE(opts.lint_only);
  EXPECT_FALSE(opts.parse_only);
}

TEST(CompilationUnitOptions, PerFileOptionSelectsTheSeparateModel) {
  CliOptions opts;
  EXPECT_TRUE(
      ParseCommandLine({"--compilation-unit-per-file", "a.sv", "b.sv"}, opts));
  EXPECT_TRUE(opts.compilation_unit_per_file);
  EXPECT_EQ(opts.source_files.size(), 2u);
}

TEST(CompilationUnitOptions, WithoutTheOptionEveryFileIsOneUnit) {
  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine({"a.sv", "b.sv"}, opts));
  EXPECT_FALSE(opts.compilation_unit_per_file);
}

TEST(RunStageOptions, NoStageOptionLeavesBothUnset) {
  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine({"--top", "m", "m.sv"}, opts));
  EXPECT_FALSE(opts.parse_only);
  EXPECT_FALSE(opts.lint_only);
}

TEST(NumericOptions, NumberWrittenLastIsReportedAsMissingItsValue) {
  for (const char* name : {"--seed", "--max-generate-iterations",
                           "--pulse-reject-limit", "--pulse-error-limit"}) {
    CliOptions opts;
    std::string err;
    EXPECT_FALSE(ParseCommandLineCapturingStderr({"m.sv", name}, opts, err))
        << name;
    EXPECT_TRUE(opts.rejected_argument) << name;
    EXPECT_NE(err.find(std::string(name) + " expects a value"),
              std::string::npos)
        << err;
    EXPECT_EQ(err.find("unknown option"), std::string::npos) << err;
  }
}

TEST(NumericOptions, NegativeNumberIsRefused) {
  for (const char* name : {"--seed", "--max-generate-iterations"}) {
    CliOptions opts;
    std::string err;
    EXPECT_FALSE(ParseCommandLineCapturingStderr({name, "-1"}, opts, err))
        << name;
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

TEST(MinTypMaxOption, TypWrittenAfterMinSelectsTyp) {
  CliOptions opts;
  EXPECT_TRUE(
      ParseCommandLine({"--mintypmax", "min", "--mintypmax", "typ"}, opts));
  EXPECT_EQ(opts.mintypmax, DelayMode::kTyp);
  EXPECT_FALSE(opts.rejected_argument);
}

TEST(ValueOptions, EachNameReachesItsOwnField) {
  const std::pair<const char*, std::string CliOptions::*> kOptions[] = {
      {"--vcd", &CliOptions::vcd_file}, {"--config", &CliOptions::config}};
  for (const auto& [name, field] : kOptions) {
    CliOptions opts;
    EXPECT_TRUE(ParseCommandLine({name, name}, opts)) << name;
    for (const auto& [other, other_field] : kOptions) {
      EXPECT_EQ(opts.*other_field, std::string_view(other) == name ? name : "")
          << name << " as seen in " << other;
    }
    EXPECT_TRUE(opts.top_modules.empty()) << name << " as seen in --top";
  }
  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine({"--top", "--top"}, opts));
  EXPECT_EQ(opts.top_modules, std::vector<std::string>{"--top"});
  for (const auto& [other, other_field] : kOptions) {
    EXPECT_EQ(opts.*other_field, "") << "--top as seen in " << other;
  }
}

TEST(RemovedOptions, EachIsReportedAsAnUnknownOption) {
  for (const char* name : {"-o", "--timescale", "--fst", "--max-time", "-v",
                           "-y", "-Wall", "--target", "--lut-size", "--lib",
                           "--format", "--area", "--delay", "--retime"}) {
    CliOptions opts;
    std::string err;
    EXPECT_FALSE(ParseCommandLineCapturingStderr({name}, opts, err)) << name;
    EXPECT_FALSE(opts.rejected_argument) << name;
    EXPECT_NE(err.find(std::string("unknown option: ") + name),
              std::string::npos)
        << err;
  }
}

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

TEST(DefineOption, JoinedAndSeparateDefinitionsBothReachTheDefines) {
  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine({"-DWIDTH=8", "-D", "FAST"}, opts));
  EXPECT_EQ(opts.defines, (std::vector<std::pair<std::string, std::string>>{
                              {"WIDTH", "8"}, {"FAST", "1"}}));
}

TEST(DefineOption, DefineWrittenLastIsReportedAsMissingItsValue) {
  CliOptions opts;
  std::string err;
  EXPECT_FALSE(ParseCommandLineCapturingStderr({"m.sv", "-D"}, opts, err));
  EXPECT_TRUE(opts.rejected_argument);
  EXPECT_NE(err.find("-D expects a value"), std::string::npos) << err;
  EXPECT_TRUE(opts.defines.empty());
}

TEST(ProtectOptions, RefusedNamedKeyFailsTheParse) {
  CliOptions opts;
  std::string err;
  EXPECT_FALSE(ParseCommandLineCapturingStderr({"--protect-named-key", "acme"},
                                               opts, err));
  EXPECT_TRUE(opts.protect.rejected_argument);
  EXPECT_TRUE(opts.rejected_argument);
  EXPECT_NE(err.find("--protect-named-key expects <owner>:<name>=<key>: acme"),
            std::string::npos)
      << err;

  CliOptions accepted;
  EXPECT_TRUE(ParseCommandLine({"--protect-named-key", "acme:k=s3"}, accepted));
  EXPECT_FALSE(accepted.rejected_argument);
}

TEST(OptionsFile, FileThatCannotBeOpenedStopsTheParse) {
  ScratchDir tmp;
  const std::string kAbsent = (tmp.dir / "absent.f").string();

  CliOptions opts;
  std::string err;
  EXPECT_FALSE(
      ParseCommandLineCapturingStderr({"-f", kAbsent, "m.sv"}, opts, err));
  EXPECT_NE(err.find("cannot open options file '" + kAbsent + "'"),
            std::string::npos)
      << err;
  EXPECT_TRUE(opts.source_files.empty());
}

TEST(OptionsFile, HashWordCommentsOutTheRestOfItsLine) {
  ScratchDir tmp;
  const std::string kOptionsFile =
      tmp.Write("args.f", "--top adder #--seed 9\n--seed 7 a#b.sv\n").string();

  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine({"-f", kOptionsFile}, opts));
  EXPECT_EQ(opts.top_modules, std::vector<std::string>{"adder"});
  EXPECT_EQ(opts.seed, 7U);
  EXPECT_EQ(opts.source_files, std::vector<std::string>{"a#b.sv"});
}

}  // namespace

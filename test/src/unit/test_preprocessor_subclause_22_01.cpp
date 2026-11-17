#include <gtest/gtest.h>

#include <fstream>
#include <string>

#include "fixture_preprocessor.h"
#include "fixture_scratch_dir.h"
#include "helpers_reported_error.h"

namespace {

struct DirectiveUse {
  const char* name;
  const char* text;
};

const DirectiveUse kEveryDirectiveTheClauseDescribes[] = {
    {"__FILE__", "string f = `__FILE__;\n"},
    {"__LINE__", "int l = `__LINE__;\n"},
    {"begin_keywords", "`begin_keywords \"1800-2023\"\n"},
    {"celldefine", "`celldefine\n"},
    {"default_nettype", "`default_nettype wire\n"},
    {"define", "`define M 1\n"},
    {"else", "`ifdef NOT_DEFINED\n`else\n`endif\n"},
    {"elsif", "`ifdef NOT_DEFINED\n`elsif NOT_DEFINED\n`endif\n"},
    {"end_keywords", "`begin_keywords \"1800-2023\"\n`end_keywords\n"},
    {"endcelldefine", "`celldefine\n`endcelldefine\n"},
    {"endif", "`ifdef NOT_DEFINED\n`endif\n"},
    {"ifdef", "`ifdef NOT_DEFINED\n`endif\n"},
    {"ifndef", "`ifndef NOT_DEFINED\n`endif\n"},
    {"include", "`include \"listed.svh\"\n"},
    {"line", "`line 10 \"named.sv\" 0\n"},
    {"nounconnected_drive", "`nounconnected_drive\n"},
    {"pragma", "`pragma listed_pragma\n"},
    {"resetall", "`resetall\n"},
    {"timescale", "`timescale 1ns / 1ps\n"},
    {"unconnected_drive", "`unconnected_drive pull1\n`nounconnected_drive\n"},
    {"undef", "`define M 1\n`undef M\n"},
    {"undefineall", "`undefineall\n"},
};

TEST(CompilerDirectiveSet, EveryListedDirectiveIsProcessedAsADirective) {
  ScratchWorkingDir scratch;
  {
    std::ofstream inc(scratch.dir / "listed.svh");
    inc << "\n";
  }
  for (const auto& use : kEveryDirectiveTheClauseDescribes) {
    PreprocFixture f;
    auto out = Preprocess(use.text, f);
    EXPECT_TRUE(f.diag.Diagnostics().empty()) << "`" << use.name;
    EXPECT_EQ(out.find(std::string("`") + use.name), std::string::npos)
        << "`" << use.name << " left in the output:\n"
        << out;
  }
}

TEST(CompilerDirectiveSet, AnUnlistedUndefinedNameIsNotADirective) {
  PreprocFixture f;
  Preprocess("`not_a_listed_directive\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "undefined macro 'not_a_listed_directive'", 1,
                            "22.5.1"));
}

}  // namespace

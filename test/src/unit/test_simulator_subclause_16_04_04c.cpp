#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/cover_results.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

const char kSay[] =
    "  function void say(input string s); $display(\"%0t %s\", $time, s); "
    "endfunction\n";

std::string Module(const std::string& items, const std::string& outside = "") {
  return outside +
         "module t;\n"
         "  logic a = 0, en = 1, q, clk = 0, started = 0;\n"
         "  event never;\n" +
         kSay + items + "endmodule\n";
}

std::string Captured(const std::string& src) {
  SimFixture f;
  std::string out = RunCapture(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  return out;
}

std::string HeldProcedure(const std::string& assertion,
                          const std::string& name = "p") {
  return "  initial begin : " + name + "\n    " + assertion +
         ";\n    @(never);\n  end\n";
}

TEST(DisableOutermostScopeLive, AnotherProcessFlushesAssumeAndCoverReports) {
  for (const char* assertion :
       {"assume #0 (0) else say(\"p\")", "c: cover #0 (1) say(\"p\")"}) {
    SimFixture f;
    EXPECT_EQ(
        RunCapture(
            Module(HeldProcedure(assertion) + "  initial #0 disable p;\n"), f),
        "")
        << assertion;
    for (const auto& r : f.ctx.ImmediateCovers().Results()) {
      EXPECT_EQ(r.succeeded, 0u) << r.scope;
    }
  }
}

TEST(DisableOutermostScopeLive, AnotherProcessFlushesEveryProcedureKind) {
  for (const char* items : {"  always_comb begin : p\n"
                            "    q = a;\n"
                            "    assert #0 (a) else say(\"p\");\n"
                            "  end\n"
                            "  initial #0 disable p;\n",
                            "  always_latch begin : p\n"
                            "    if (en) q = a;\n"
                            "    assert #0 (a) else say(\"p\");\n"
                            "  end\n"
                            "  initial #0 disable p;\n",
                            "  always_ff @(posedge clk) begin : p\n"
                            "    assert #0 (0) else say(\"p\");\n"
                            "  end\n"
                            "  initial begin #1 clk = 1; #0 disable p; end\n",
                            "  initial fork : p\n"
                            "    begin assert #0 (0) else say(\"p\"); end\n"
                            "    @(never);\n"
                            "  join\n"
                            "  initial #0 disable p;\n"}) {
    EXPECT_EQ(Captured(Module(items)), "") << items;
  }
}

TEST(DisableOutermostScopeLive, AnotherProcessFlushesAnInstancesProcedure) {
  EXPECT_EQ(Captured(Module(
                "  ifc i();\n  initial #0 disable i.pi;\n",
                std::string("interface ifc;\n  event never;\n") + kSay +
                    HeldProcedure("assert #0 (0) else say(\"pi\")", "pi") +
                    "endinterface\n")),
            "");
  EXPECT_EQ(Captured(Module(
                "  sub s();\n  initial #0 disable s.ps;\n",
                std::string("module sub;\n  event never;\n") + kSay +
                    HeldProcedure("assert #0 (0) else say(\"ps\")", "ps") +
                    "endmodule\n")),
            "");
}

TEST(DisableOutermostScopeLive, AnotherProgramProcessFlushesAProgramProcedure) {
  EXPECT_EQ(Captured(std::string("program pg;\n  logic started = 0;\n"
                                 "  event never;\n") +
                     kSay +
                     "  initial begin : pp\n"
                     "    assert #0 (0) else say(\"pp\");\n"
                     "    started = 1;\n"
                     "    @(never);\n"
                     "  end\n"
                     "  initial begin wait (started); disable pp; end\n"
                     "endprogram\n"),
            "");
}

TEST(DisableOutermostScopeLive, DISABLED_ASelfDisableFlushesEveryReportKind) {
  for (const char* assertion :
       {"assert #0 (0) else say(\"p\");", "assert final (0) else say(\"p\");",
        "assume #0 (0) else say(\"p\");", "assert #0 (0);",
        "c: cover #0 (1) say(\"p\");",
        "assert #0 (0) else say(\"p1\"); assert #0 (0) else say(\"p2\");"}) {
    SimFixture f;
    EXPECT_EQ(RunCapture(Module(std::string("  initial begin : p\n    ") +
                                assertion + "\n    disable p;\n  end\n"),
                         f),
              "")
        << assertion;
    EXPECT_EQ(f.ctx.LastSeverity(), "") << assertion;
    for (const auto& r : f.ctx.ImmediateCovers().Results()) {
      EXPECT_EQ(r.succeeded, 0u) << r.scope;
    }
  }
}

TEST(DisableOutermostScopeLive, DISABLED_AnAlwaysSelfDisableFlushesAndRearms) {
  EXPECT_EQ(Captured(Module("  always @(a) begin : p\n"
                            "    say(\"p ran\");\n"
                            "    assert #0 (0) else say(\"p reported\");\n"
                            "    disable p;\n"
                            "  end\n"
                            "  initial begin #1 a = 1; #1 a = 0; end\n")),
            "1 p ran\n2 p ran\n");
}

TEST(DisableOutermostScopeLive,
     DISABLED_ASelfDisableFromANestedBlockOrACalledTaskFlushes) {
  for (const char* items : {"  initial begin : p\n"
                            "    begin : inner\n"
                            "      assert #0 (0) else say(\"p\");\n"
                            "      disable p;\n"
                            "    end\n"
                            "  end\n",
                            "  task kill; disable p; endtask\n"
                            "  initial begin : p\n"
                            "    assert #0 (0) else say(\"p\");\n"
                            "    kill();\n"
                            "  end\n"}) {
    EXPECT_EQ(Captured(Module(items)), "") << items;
  }
}

TEST(DisableOutermostScopeLive, ABranchDisablingItsForkJoinFlushes) {
  EXPECT_EQ(Captured(Module("  initial fork : p\n"
                            "    begin assert #0 (0) else say(\"p\"); "
                            "@(never); end\n"
                            "    disable p;\n"
                            "  join\n")),
            "");
}

TEST(DisableOutermostScopeLive, DISABLED_AProgramProcedureSelfDisableFlushes) {
  EXPECT_EQ(Captured(std::string("program pg;\n") + kSay +
                     "  initial begin : pp\n"
                     "    assert #0 (0) else say(\"pp\");\n"
                     "    disable pp;\n"
                     "  end\n"
                     "endprogram\n"),
            "");
}

TEST(DisableNonOutermostScopeLive, TaskDisableDoesNotFlushAFinalReport) {
  EXPECT_EQ(Captured(Module("  task tk;\n"
                            "    disable tk;\n"
                            "  endtask\n"
                            "  initial begin : p\n"
                            "    assert final (0) else say(\"p\");\n"
                            "    tk();\n"
                            "  end\n")),
            "0 p\n");
}

TEST(DisableNonOutermostScopeLive,
     AnInnerBlockDisabledFromOutsideKeepsReports) {
  EXPECT_EQ(Captured(Module("  initial begin : p\n"
                            "    begin : inner\n"
                            "      assert #0 (0) else say(\"p\");\n"
                            "      @(never);\n"
                            "    end\n"
                            "  end\n"
                            "  initial #0 disable p.inner;\n")),
            "0 p\n");
}

}  // namespace

#include <algorithm>
#include <string>
#include <utility>
#include <vector>

// Completes the CoverageDB type that sim_context.h only forward-declares;
// included ahead of the fixtures so SimContext's inline constructor (whose
// unwind path destroys the owned coverage database) is well-formed in this TU.
#include "fixture_simulator.h"
#include "fixture_vcd.h"
#include "helpers_vcd_dump.h"
#include "simulator/coverage.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

// §21.7.1.5: limiting the size of the dump file with $dumplimit. Each test
// drives real source through parse, elaboration, lowering, and the scheduler,
// with the design's own variables registered on a real writer and the driver's
// per-timestep recording loop installed (timestamp + changed values at the end
// of each time unit, the way the simulation driver dumps). This is what lets
// the byte budget, the stop, and the limit comment be observed as the
// production task path and writer apply them, rather than by hand-driving the
// writer or hand-seeding previous values.
class DumplimitSysTask : public VcdTestBase {
 protected:
  std::string RunVcd(const std::string& src) {
    SimFixture f;
    auto* design = ElaborateSrc(src, f);
    if (design == nullptr) return "<elaboration-failed>";
    Lowerer lowerer(f.ctx, f.arena, f.diag);
    lowerer.Lower(design);
    {
      VcdWriter vcd(tmp_path_);
      vcd.WriteHeader("1ns");
      // Register in name order so identifier codes are deterministic: the
      // alphabetically first variable gets '!', the next '"', and so on.
      std::vector<std::pair<std::string_view, Variable*>> vars(
          f.ctx.GetVariables().begin(), f.ctx.GetVariables().end());
      std::sort(vars.begin(), vars.end(),
                [](const auto& a, const auto& b) { return a.first < b.first; });
      for (const auto& [name, var] : vars) {
        vcd.RegisterSignal(name, var->value.width, var);
      }
      vcd.EndDefinitions();
      // Value change dumping starts once the source's $dumpvars executes.
      vcd.ArmDumpvarsStart();
      f.ctx.SetVcdWriter(&vcd);
      f.scheduler.SetPostTimestepCallback([&vcd, &f]() {
        vcd.WriteTimestamp(f.ctx.CurrentTime().ticks);
        vcd.DumpChangedValues(0);
      });
      f.scheduler.Run();
    }  // writer destructor flushes the dump to tmp_path_ before ReadVcd
    return ReadVcd();
  }

  // Counts the value-change-section timestamps (#<time> lines) in a dump.
  static std::size_t CountTimestamps(const std::string& content) {
    return CountOccurrences(content, "\n#");
  }
};

// The core rule: once the file reaches the filesize byte count the dumping
// stops and a comment noting the limit is inserted, while value changes
// recorded below the budget are retained.
TEST_F(DumplimitSysTask, LimitReachedStopsDumpAndInsertsComment) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h00;\n"
      "    $dumplimit(200);\n"
      "    $dumpvars;\n"
      "    repeat (40) #10 data = data + 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("#10\n"), std::string::npos);  // early dump retained
  // The marker is a proper VCD comment section: the limit text sits between
  // the $comment keyword and its closing $end.
  auto comment = content.find("$comment");
  ASSERT_NE(comment, std::string::npos);
  auto text = content.find("Dump limit of", comment);
  ASSERT_NE(text, std::string::npos);
  EXPECT_LT(text, content.find("$end", comment));
  EXPECT_EQ(content.find("#400\n"), std::string::npos);  // late dumps stopped
}

// "The dumping stops" means the comment is the file's final section: no
// timestamp or value change is recorded after the limit marker.
TEST_F(DumplimitSysTask, NothingFollowsTheLimitComment) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h00;\n"
      "    $dumplimit(200);\n"
      "    $dumpvars;\n"
      "    repeat (40) #10 data = data + 1;\n"
      "  end\n"
      "endmodule\n");
  auto pos = content.find("Dump limit of");
  ASSERT_NE(pos, std::string::npos);
  // The comment text carries no '#', so any '#' past it would be a timestamp
  // recorded after the dump was supposed to have stopped.
  EXPECT_EQ(content.find('#', pos), std::string::npos);
}

// The stop is latched: despite dozens of post-limit dump attempts, the marker
// comment is inserted exactly once, when the threshold is first crossed.
TEST_F(DumplimitSysTask, LimitCommentInsertedOnlyOnce) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h00;\n"
      "    $dumplimit(200);\n"
      "    $dumpvars;\n"
      "    repeat (40) #10 data = data + 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(CountOccurrences(content, "Dump limit of"), 1u);
}

// Negative: a budget the file never reaches leaves the dump untouched -- every
// value change of the same workload is recorded and no limit comment appears.
TEST_F(DumplimitSysTask, BelowLimitDumpingContinuesWithoutComment) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h00;\n"
      "    $dumplimit(1000000);\n"
      "    $dumpvars;\n"
      "    repeat (40) #10 data = data + 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(content.find("$comment"), std::string::npos);  // no limit comment
  EXPECT_NE(content.find("#400\n"), std::string::npos);    // last change kept
}

// The filesize argument is a count of bytes: with the same workload, a larger
// byte budget records strictly more of the dump before stopping than a smaller
// one, and both runs stop with the marker.
TEST_F(DumplimitSysTask, LargerByteBudgetRecordsMoreOfTheDump) {
  const char* kSmall =
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h00;\n"
      "    $dumplimit(200);\n"
      "    $dumpvars;\n"
      "    repeat (40) #10 data = data + 1;\n"
      "  end\n"
      "endmodule\n";
  const char* kLarge =
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h00;\n"
      "    $dumplimit(400);\n"
      "    $dumpvars;\n"
      "    repeat (40) #10 data = data + 1;\n"
      "  end\n"
      "endmodule\n";
  auto small = RunVcd(kSmall);
  auto small_count = CountTimestamps(small);
  ASSERT_NE(small.find("Dump limit of 200"), std::string::npos);
  auto large = RunVcd(kLarge);
  ASSERT_NE(large.find("Dump limit of 400"), std::string::npos);
  EXPECT_GT(CountTimestamps(large), small_count);
}

// The byte count is compared against the file's current size whenever a dump
// is attempted: a budget set mid-simulation that the already-written content
// exceeds stops the dump at the very next recording attempt -- the end of the
// same time unit in which $dumplimit executed.
TEST_F(DumplimitSysTask, MidSimulationLimitAppliesToBytesAlreadyWritten) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h00;\n"
      "    $dumpvars;\n"
      "    repeat (10) #10 data = data + 1;\n"
      "    $dumplimit(1);\n"
      "    repeat (10) #10 data = data + 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("#90\n"),
            std::string::npos);  // pre-limit content stands
  EXPECT_NE(content.find("Dump limit of 1 "), std::string::npos);
  // The recording attempt at the end of the $dumplimit time unit (#100) is
  // already over budget, so it and everything later are dropped.
  EXPECT_EQ(content.find("#100\n"), std::string::npos);
}

// filesize produced by a parameter: the elaborated constant is the byte
// budget, so the small parameterized limit stops the dump.
TEST_F(DumplimitSysTask, FilesizeFromParameter) {
  auto content = RunVcd(
      "module t;\n"
      "  parameter LIMIT = 200;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h00;\n"
      "    $dumplimit(LIMIT);\n"
      "    $dumpvars;\n"
      "    repeat (40) #10 data = data + 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("Dump limit of 200"), std::string::npos);
  EXPECT_EQ(content.find("#400\n"), std::string::npos);
}

// filesize produced by a localparam behaves the same way.
TEST_F(DumplimitSysTask, FilesizeFromLocalparam) {
  auto content = RunVcd(
      "module t;\n"
      "  localparam LIMIT = 200;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h00;\n"
      "    $dumplimit(LIMIT);\n"
      "    $dumpvars;\n"
      "    repeat (40) #10 data = data + 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("Dump limit of 200"), std::string::npos);
  EXPECT_EQ(content.find("#400\n"), std::string::npos);
}

// filesize produced by a run-time variable: the value the variable holds when
// $dumplimit executes is the budget.
TEST_F(DumplimitSysTask, FilesizeFromVariable) {
  auto content = RunVcd(
      "module t;\n"
      "  int lim;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h00;\n"
      "    lim = 200;\n"
      "    $dumplimit(lim);\n"
      "    $dumpvars;\n"
      "    repeat (40) #10 data = data + 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("Dump limit of 200"), std::string::npos);
  EXPECT_EQ(content.find("#400\n"), std::string::npos);
}

// filesize produced by an arithmetic expression: the evaluated result is the
// budget.
TEST_F(DumplimitSysTask, FilesizeFromExpression) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h00;\n"
      "    $dumplimit(100 + 100);\n"
      "    $dumpvars;\n"
      "    repeat (40) #10 data = data + 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("Dump limit of 200"), std::string::npos);
  EXPECT_EQ(content.find("#400\n"), std::string::npos);
}

// The full source idiom of the dump-task family: $dumpfile (§21.7.1.1) names
// the file and $dumpvars (§21.7.1.2) selects and starts the dump, both from
// real source syntax, with $dumplimit bounding the dump they produce. The
// limit is enforced with the whole sequence routed through the production
// system-call dispatch.
TEST_F(DumplimitSysTask, DumplimitAfterDumpfileAndDumpvarsSequence) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    $dumpfile(\"dump1.dump\");\n"
      "    data = 8'h00;\n"
      "    $dumplimit(200);\n"
      "    $dumpvars;\n"
      "    repeat (40) #10 data = data + 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("#10\n"), std::string::npos);
  EXPECT_NE(content.find("Dump limit of 200"), std::string::npos);
  EXPECT_EQ(content.find("#400\n"), std::string::npos);
}

// The task is an ordinary task enable: setting the budget from a task body
// bounds the dump the same way.
TEST_F(DumplimitSysTask, DumplimitInvokedFromTaskBody) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  task cap;\n"
      "    $dumplimit(200);\n"
      "  endtask\n"
      "  initial begin\n"
      "    data = 8'h00;\n"
      "    cap;\n"
      "    $dumpvars;\n"
      "    repeat (40) #10 data = data + 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("Dump limit of 200"), std::string::npos);
  EXPECT_EQ(content.find("#400\n"), std::string::npos);
}

// Negative: with no dump file in place, executing $dumplimit is harmless --
// the design still runs to completion without errors.
TEST_F(DumplimitSysTask, WithoutDumpFileDumplimitIsHarmless) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h11;\n"
      "    #10 $dumplimit(200);\n"
      "    #10 data = 8'h22;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.GetVcdWriter(), nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
}  // namespace delta

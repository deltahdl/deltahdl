#include <algorithm>
#include <string>
#include <utility>
#include <vector>

// Completes the CoverageDB type that sim_context.h only forward-declares;
// included ahead of the fixtures so SimContext's inline constructor (whose
// unwind path destroys the owned coverage database) is well-formed in this TU.
#include "fixture_simulator.h"
#include "fixture_vcd.h"
#include "simulator/coverage.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

// Exercises $dumpportslimit (§21.7.3.4) end to end: every test drives real
// source through parse, elaboration, lowering, and the scheduler with the
// driver's per-timestep recording loop installed, so the byte budget, the
// stop, and the limit comment are observed as the production task path applies
// them to a dump opened by a real $dumpports call (§21.7.3.1). The size-limit
// mechanics themselves are the 4-state machinery the extended VCD file
// inherits (§21.7.1.5).
class DumpportslimitSysTask : public VcdTestBase {
 protected:
  // Runs the source through the full pipeline with the driver's dump loop
  // (timestamp + changed values at the end of each time unit) and returns the
  // dump file contents. The fixture is caller-owned so its diagnostics and
  // context stay inspectable after the run.
  std::string RunVcd(SimFixture& f, const std::string& src) {
    auto* design = ElaborateSrc(src, f);
    if (design == nullptr) return "<elaboration-failed>";
    Lowerer lowerer(f.ctx, f.arena, f.diag);
    lowerer.Lower(design);
    {
      VcdWriter vcd(tmp_path_);
      vcd.WriteHeader("1ns");
      vcd.BeginScope("t");
      // Register in name order so identifier codes are deterministic: the
      // alphabetically first variable gets '!', the next '"', and so on.
      std::vector<std::pair<std::string_view, Variable*>> vars(
          f.ctx.GetVariables().begin(), f.ctx.GetVariables().end());
      std::sort(vars.begin(), vars.end(),
                [](const auto& a, const auto& b) { return a.first < b.first; });
      for (const auto& [name, var] : vars) {
        vcd.RegisterSignal(name, var->value.width, var);
      }
      vcd.EndScope();
      vcd.EndDefinitions();
      // Value change dumping starts only once the source's $dumpports call
      // schedules its opening checkpoint.
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
};

// §21.7.3.4: once the port dump reaches the filesize byte count, the dumping
// stops and a comment noting the limit was attained is inserted into the file
// as a proper $comment ... $end section, while value changes recorded below
// the budget are retained.
TEST_F(DumpportslimitSysTask, LimitReachedStopsPortDumpAndInsertsComment) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit(300, \"p.dump\");\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("#10\n"), std::string::npos);  // early dump retained
  auto comment = content.find("$comment");
  ASSERT_NE(comment, std::string::npos);
  auto text = content.find("Dump limit of 300", comment);
  ASSERT_NE(text, std::string::npos);
  EXPECT_LT(text, content.find("$end", comment));
  EXPECT_EQ(content.find("#400\n"), std::string::npos);  // late dumps stopped
}

// §21.7.3.4: "the dumping stops" means the limit comment is the file's final
// section -- no timestamp or port value change is recorded after it.
TEST_F(DumpportslimitSysTask, NothingFollowsTheLimitComment) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit(300, \"p.dump\");\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  auto pos = content.find("Dump limit of");
  ASSERT_NE(pos, std::string::npos);
  // The comment text carries no '#', so any '#' past it would be a timestamp
  // recorded after the dump was supposed to have stopped.
  EXPECT_EQ(content.find('#', pos), std::string::npos);
}

// §21.7.3.4 negative control: a byte budget the port dump never approaches
// leaves it untouched -- every value change of the same workload is recorded
// and no limit comment appears, showing the filesize value the task is given
// controls the outcome.
TEST_F(DumpportslimitSysTask, BelowLimitDumpingContinuesWithoutComment) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit(1000000, \"p.dump\");\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$comment"), std::string::npos);  // no limit comment
  EXPECT_NE(content.find("#400\n"), std::string::npos);    // last change kept
}

// §21.7.3.4: with no filename, the filesize limit applies to all files opened
// for dumping by calls to $dumpports -- the one-argument form bounds the open
// port dump.
TEST_F(DumpportslimitSysTask, NoFilenameLimitAppliesToAllDumpportsFiles) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit(300);\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("Dump limit of 300"), std::string::npos);
  EXPECT_EQ(content.find("#400\n"), std::string::npos);
}

// §21.7.3.4: the filesize is an integer argument; one produced by an
// elaborated parameter constant is the byte budget.
TEST_F(DumpportslimitSysTask, FilesizeFromParameter) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  parameter LIMIT = 300;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit(LIMIT, \"p.dump\");\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("Dump limit of 300"), std::string::npos);
  EXPECT_EQ(content.find("#400\n"), std::string::npos);
}

// §21.7.3.4: a localparam constant supplies the filesize the same way.
TEST_F(DumpportslimitSysTask, FilesizeFromLocalparam) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  localparam LIMIT = 300;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit(LIMIT, \"p.dump\");\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("Dump limit of 300"), std::string::npos);
  EXPECT_EQ(content.find("#400\n"), std::string::npos);
}

// §21.7.3.4: the filesize may come from a run-time variable filled by its
// declaration initializer; the value held when the task executes is the
// budget.
TEST_F(DumpportslimitSysTask, FilesizeFromVariableDeclInitializer) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  int lim = 300;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit(lim, \"p.dump\");\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("Dump limit of 300"), std::string::npos);
  EXPECT_EQ(content.find("#400\n"), std::string::npos);
}

// §21.7.3.4: the filesize variable may equally be filled by a procedural
// assignment before the task executes.
TEST_F(DumpportslimitSysTask, FilesizeFromVariableProceduralAssignment) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  int lim;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    lim = 300;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit(lim, \"p.dump\");\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("Dump limit of 300"), std::string::npos);
  EXPECT_EQ(content.find("#400\n"), std::string::npos);
}

// §21.7.3.4: the filesize argument is an expression; an arithmetic expression
// evaluates to the byte budget.
TEST_F(DumpportslimitSysTask, FilesizeFromExpression) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit(100 + 200, \"p.dump\");\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("Dump limit of 300"), std::string::npos);
  EXPECT_EQ(content.find("#400\n"), std::string::npos);
}

// §21.7.3.4: the filename may be a string-typed variable -- here filled by a
// procedural assignment -- holding the name given to $dumpports; the dump it
// names is bounded.
TEST_F(DumpportslimitSysTask, FilenameFromStringVariableProceduralAssignment) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  string fn;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    fn = \"p.dump\";\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit(300, fn);\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("Dump limit of 300"), std::string::npos);
  EXPECT_EQ(content.find("#400\n"), std::string::npos);
}

// §21.7.3.4: the string-typed filename variable may equally be filled by its
// declaration initializer.
TEST_F(DumpportslimitSysTask, FilenameFromStringVariableDeclInitializer) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  string fn = \"p.dump\";\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit(300, fn);\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("Dump limit of 300"), std::string::npos);
  EXPECT_EQ(content.find("#400\n"), std::string::npos);
}

// §21.7.3.4: the filename may equally be an integral variable containing a
// character string naming the $dumpports dump to bound.
TEST_F(DumpportslimitSysTask, FilenameFromIntegralVariable) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [47:0] fn = \"p.dump\";\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit(300, fn);\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("Dump limit of 300"), std::string::npos);
  EXPECT_EQ(content.find("#400\n"), std::string::npos);
}

// §21.7.3.4: the integral filename variable may equally be filled by a
// procedural assignment before the task executes; the character string it
// holds names the $dumpports dump to bound.
TEST_F(DumpportslimitSysTask,
       FilenameFromIntegralVariableProceduralAssignment) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [47:0] fn;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    fn = \"p.dump\";\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit(300, fn);\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("Dump limit of 300"), std::string::npos);
  EXPECT_EQ(content.find("#400\n"), std::string::npos);
}

// §21.7.3.4 negative: the filename denotes a file specified in a $dumpports
// call, so a name matching no $dumpports output leaves the task ignored
// (general rule of §21.7.3.7): no byte budget is installed, the dump runs
// past it, and no limit comment appears.
TEST_F(DumpportslimitSysTask, UnknownFilenameLeavesDumpUnlimited) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit(300, \"other.vcd\");\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$comment"), std::string::npos);
  EXPECT_NE(content.find("#400\n"), std::string::npos);  // still dumping
}

// §21.7.3.4 negative: the unknown-file rule sees through a variable-held name
// too -- a string variable naming no $dumpports output installs no limit.
TEST_F(DumpportslimitSysTask, UnknownFilenameInVariableLeavesDumpUnlimited) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  string fn = \"other.vcd\";\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit(300, fn);\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$comment"), std::string::npos);
  EXPECT_NE(content.find("#400\n"), std::string::npos);  // still dumping
}

// §21.7.3.4 negative: the filesize argument is required. The bare call names
// no byte budget, so it is reported as an error and no limit takes effect --
// the dump keeps recording.
TEST_F(DumpportslimitSysTask, MissingFilesizeIsReported) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit;\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_TRUE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$comment"), std::string::npos);
  EXPECT_NE(content.find("#400\n"), std::string::npos);  // still dumping
}

// §21.7.3.4 negative: the empty parenthesized form carries no filesize either
// and is reported the same way.
TEST_F(DumpportslimitSysTask, MissingFilesizeEmptyParenIsReported) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit();\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_TRUE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$comment"), std::string::npos);
}

// §21.7.3.4 negative: supplying only the filename with a null first argument
// still omits the required filesize, so the call is reported and no budget is
// installed even though the named file is a live $dumpports output.
TEST_F(DumpportslimitSysTask, NullFilesizeWithFilenameIsReported) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit(, \"p.dump\");\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_TRUE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$comment"), std::string::npos);
  EXPECT_NE(content.find("#400\n"), std::string::npos);  // still dumping
}

// §21.7.3.4: the filesize counts bytes -- with the same port-dump workload a
// larger byte budget records strictly more of the dump before the stop, and
// each run's limit comment names its own budget.
TEST_F(DumpportslimitSysTask, LargerByteBudgetRecordsMoreOfTheDump) {
  auto count_timestamps = [](const std::string& content) {
    std::size_t n = 0;
    for (auto pos = content.find("\n#"); pos != std::string::npos;
         pos = content.find("\n#", pos + 1)) {
      ++n;
    }
    return n;
  };
  auto src = [](const char* limit) {
    return std::string(
               "module t;\n"
               "  logic [7:0] d;\n"
               "  initial begin\n"
               "    d = 8'h00;\n"
               "    $dumpports(, \"p.dump\");\n"
               "    $dumpportslimit(") +
           limit +
           ", \"p.dump\");\n"
           "    repeat (40) #10 d = d + 1;\n"
           "  end\n"
           "endmodule\n";
  };
  SimFixture f_small;
  auto small = RunVcd(f_small, src("300"));
  EXPECT_FALSE(f_small.diag.HasErrors());
  ASSERT_NE(small.find("Dump limit of 300"), std::string::npos);
  SimFixture f_large;
  auto large = RunVcd(f_large, src("450"));
  EXPECT_FALSE(f_large.diag.HasErrors());
  ASSERT_NE(large.find("Dump limit of 450"), std::string::npos);
  EXPECT_GT(count_timestamps(large), count_timestamps(small));
}

// §21.7.3.4 edge: with no dump file in place, executing $dumpportslimit with a
// proper filesize is harmless -- the design runs to completion without errors.
TEST_F(DumpportslimitSysTask, WithoutDumpFileIsHarmless) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] d;\n"
      "  initial begin\n"
      "    d = 8'h11;\n"
      "    #10 $dumpportslimit(300);\n"
      "    #10 d = 8'h22;\n"
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

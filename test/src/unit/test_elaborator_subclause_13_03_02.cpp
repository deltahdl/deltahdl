#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(TaskBodyElaboration, AutoTaskLocalInNonblockingAssignError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task automatic t();\n"
      "    int x;\n"
      "    x <= 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "automatic task variable in nonblocking assignment",
                            4, "13.3.2"));
}

TEST(TaskBodyElaboration, AutoTaskModuleVarNonblockingOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  task automatic t();\n"
      "    x <= 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskBodyElaboration, StaticTaskLocalInNonblockingOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task static t();\n"
      "    int x;\n"
      "    x <= 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskBodyElaboration, AutoTaskArgInNonblockingAssignError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task automatic t(output int y);\n"
      "    y <= 5;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "automatic task variable in nonblocking assignment",
                            3, "13.3.2"));
}

TEST(TaskBodyElaboration, AutoTaskLocalBlockingAssignOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task automatic t();\n"
      "    int x;\n"
      "    x = 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskBodyElaboration, AutoTaskStaticLocalInNonblockingOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task automatic t();\n"
      "    static int x;\n"
      "    x <= 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskBodyElaboration, AutoTaskLocalInNestedNonblockingError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task automatic t();\n"
      "    int x;\n"
      "    if (1) begin\n"
      "      x <= 1;\n"
      "    end\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "automatic task variable in nonblocking assignment",
                            5, "13.3.2"));
}

TEST(TaskBodyElaboration, AutoTaskLocalInForceError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task automatic t();\n"
      "    int x;\n"
      "    force x = 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "automatic task variable in procedural continuous assignment", 4,
      "13.3.2"));
}

TEST(TaskBodyElaboration, AutoTaskLocalInProceduralAssignError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task automatic t();\n"
      "    int x;\n"
      "    assign x = 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "automatic task variable in procedural continuous assignment", 4,
      "13.3.2"));
}

TEST(TaskBodyElaboration, StaticTaskLocalInForceOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task static t();\n"
      "    int x;\n"
      "    force x = 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskBodyElaboration, AutoTaskLocalInNonblockingEventControlError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic q;\n"
      "  task automatic t();\n"
      "    int x;\n"
      "    q <= @(x) 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "automatic task variable in intra-assignment event control",
                    5, "13.3.2"));
}

TEST(TaskBodyElaboration, AutoTaskLocalInNonblockingRepeatEventError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, q;\n"
      "  task automatic t();\n"
      "    int n;\n"
      "    q <= repeat (n) @(posedge clk) 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "automatic task variable in intra-assignment event control",
                    5, "13.3.2"));
}

TEST(TaskBodyElaboration, AutoTaskLocalOnNonblockingRhsOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] q;\n"
      "  task automatic t();\n"
      "    int x;\n"
      "    q <= x;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskBodyElaboration, AutoTaskLocalInMonitorError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task automatic t();\n"
      "    int x;\n"
      "    $monitor(\"%d\", x);\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "automatic task variable traced by system task", 4,
                            "13.3.2"));
}

TEST(TaskBodyElaboration, AutoTaskLocalInMonitorFormsError) {
  for (const char* task :
       {"$monitorh(x)", "$fmonitor(1, x)", "$fmonitorb(1, \"%b\", x)"}) {
    ElabFixture f;
    ElaborateSrc(std::string("module m;\n"
                             "  task automatic t();\n"
                             "    int x;\n"
                             "    ") +
                     task +
                     ";\n"
                     "  endtask\n"
                     "endmodule\n",
                 f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "automatic task variable traced by system task",
                              4, "13.3.2"))
        << task;
  }
}

TEST(TaskBodyElaboration, AutoTaskLocalInStrobeAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task automatic t();\n"
      "    int x;\n"
      "    $strobe(\"%d\", x);\n"
      "    $fstrobe(1, \"%d\", x);\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskBodyElaboration, AutoTaskLocalInDumpvarsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task automatic t();\n"
      "    int x;\n"
      "    $dumpvars(0, x);\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "automatic task variable traced by system task", 4,
                            "13.3.2"));
}

TEST(TaskBodyElaboration, AutoTaskLocalInDisplayOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task automatic t();\n"
      "    int x;\n"
      "    $display(\"%d\", x);\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskBodyElaboration, AutoTaskLocalInNonblockingEventIffError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, q;\n"
      "  task automatic t();\n"
      "    logic g;\n"
      "    q <= @(posedge clk iff g) 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "automatic task variable in intra-assignment event control",
                    5, "13.3.2"));
}

TEST(TaskBodyElaboration, NonblockingEventControlModuleVarsOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, q;\n"
      "  task automatic t();\n"
      "    int x;\n"
      "    q <= @(posedge clk) 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskBodyElaboration, AutoTaskLocalInMonitorSubexpressionError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task automatic t();\n"
      "    int x;\n"
      "    $monitor(\"%d\", x + 1);\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "automatic task variable traced by system task", 4,
                            "13.3.2"));
}

TEST(TaskBodyElaboration, AutoTaskLocalBitSelectInNonblockingError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task automatic t();\n"
      "    logic [7:0] x;\n"
      "    x[0] <= 1'b1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "automatic task variable in nonblocking assignment",
                            4, "13.3.2"));
}

TEST(TaskBodyElaboration, AutoTaskLocalPartSelectInNonblockingError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task automatic t();\n"
      "    logic [7:0] x;\n"
      "    x[3:0] <= 4'h5;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "automatic task variable in nonblocking assignment",
                            4, "13.3.2"));
}

TEST(TaskBodyElaboration, ModuleVarBitSelectInNonblockingOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] q;\n"
      "  task automatic t();\n"
      "    int x;\n"
      "    q[0] <= 1'b1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskBodyElaboration, MonitorOfModuleVarOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] g;\n"
      "  task automatic t();\n"
      "    int x;\n"
      "    $monitor(\"%d\", g);\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskBodyElaboration, AutoTaskLocalInNonblockingInARandsequenceCodeBlock) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task automatic t();\n"
      "    int x;\n"
      "    randsequence(main)\n"
      "      main : { x <= 1; };\n"
      "    endsequence\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "automatic task variable in nonblocking assignment",
                            5, "13.3.2"));
}

TEST(TaskBodyElaboration,
     AutoTaskLocalInNonblockingInARandsequenceWeightCodeBlock) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task automatic t();\n"
      "    int x;\n"
      "    randsequence(main)\n"
      "      main : alt := 5 { x <= 1; };\n"
      "      alt : { ; };\n"
      "    endsequence\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "automatic task variable in nonblocking assignment",
                            5, "13.3.2"));
}

TEST(TaskBodyElaboration, AutoTaskLocalInMonitorInAForStepError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task automatic t(input int n);\n"
      "    int x;\n"
      "    int i;\n"
      "    for (i = 0; i < n; $monitor(\"%d\", x)) ;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "automatic task variable traced by system task", 5,
                            "13.3.2"));
}

TEST(TaskBodyElaboration, AutoTaskVarReadByForceOrAssignError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic g;\n"
      "  task automatic t(input logic a);\n"
      "    force g = a;\n"
      "    assign g = !a;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "automatic task variable in procedural continuous assignment", 4,
      "13.3.2"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "automatic task variable in procedural continuous assignment", 5,
      "13.3.2"));
}

}  // namespace

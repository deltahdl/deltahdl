#include "fixture_elaborator.h"

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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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

TEST(TaskBodyElaboration, StaticTaskAutoLocalInNonblockingError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task static t();\n"
      "    automatic int x;\n"
      "    x <= 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
}

// §13.3.2: an automatic task variable shall not be referenced by a force
// procedural continuous assignment.
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
  EXPECT_TRUE(f.has_errors);
}

// §13.3.2: an automatic task variable shall not be the target of a procedural
// continuous assignment.
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
  EXPECT_TRUE(f.has_errors);
}

// §13.3.2: a static-task local may legally be forced; it is not deallocated.
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

// §13.3.2: an automatic task variable shall not appear in the intra-assignment
// event control of a nonblocking assignment.
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
  EXPECT_TRUE(f.has_errors);
}

// §13.3.2: an automatic task variable shall not appear in the repeat count of a
// nonblocking-assignment intra-assignment event control.
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
  EXPECT_TRUE(f.has_errors);
}

// §13.3.2: reading an automatic task variable on the RHS of a nonblocking
// assignment to a non-automatic target is legal; the value is sampled at once.
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

// §13.3.2: an automatic task variable shall not be traced with $monitor.
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
  EXPECT_TRUE(f.has_errors);
}

// §13.3.2: an automatic task variable shall not be traced with $dumpvars.
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
  EXPECT_TRUE(f.has_errors);
}

// §13.3.2: a one-shot display of an automatic task variable is not continuous
// tracing and remains legal.
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

// §13.3.2: the prohibition on automatic task variables in an intra-assignment
// event control covers the iff guard of an event expression, not just the bare
// event signal.
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
  EXPECT_TRUE(f.has_errors);
}

// §13.3.2: an intra-assignment event control that names only non-automatic
// objects is legal; the restriction is scoped to automatic task variables.
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

// §13.3.2: the tracing prohibition reaches an automatic task variable buried in
// a larger argument expression, not only one passed directly.
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
  EXPECT_TRUE(f.has_errors);
}

// §13.3.2: assigning a bit-select of an automatic task variable with a
// nonblocking assignment writes part of that variable's storage and is therefore
// also prohibited, not just a whole-variable target.
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
  EXPECT_TRUE(f.has_errors);
}

// §13.3.2: a part-select of an automatic task variable is likewise an illegal
// nonblocking-assignment target.
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
  EXPECT_TRUE(f.has_errors);
}

// §13.3.2: a bit-select of a non-automatic (module) target remains a legal
// nonblocking-assignment target inside an automatic task.
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

// §13.3.2: tracing a non-automatic object with $monitor is legal even when an
// automatic local is in scope but not referenced by the call.
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

}

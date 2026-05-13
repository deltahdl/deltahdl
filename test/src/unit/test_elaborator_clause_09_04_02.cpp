

#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(EventControlElaboration, PosedgeEventControlElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, q, d;\n"
      "  always @(posedge clk) q <= d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(EventControlElaboration, NegedgeEventControlElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, q, d;\n"
      "  always @(negedge clk) q <= d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(EventControlElaboration, AnyChangeEventControlElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic r, q;\n"
      "  always @(r) q = r;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(EventControlElaboration, EdgeSensitivityPreservedInRtlir) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, rst_n, d, q;\n"
      "  always_ff @(posedge clk or negedge rst_n)\n"
      "    if (!rst_n) q <= 0;\n"
      "    else q <= d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  for (auto& p : design->top_modules[0]->processes) {
    if (p.kind == RtlirProcessKind::kAlwaysFF) {
      ASSERT_EQ(p.sensitivity.size(), 2u);
      EXPECT_EQ(p.sensitivity[0].edge, Edge::kPosedge);
      EXPECT_EQ(p.sensitivity[1].edge, Edge::kNegedge);
    }
  }
}

TEST(EventControlElaboration, EdgeEventControlElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, q, d;\n"
      "  always @(edge clk) q <= d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  bool found = false;
  for (auto& p : design->top_modules[0]->processes) {
    if (!p.sensitivity.empty()) {
      EXPECT_EQ(p.sensitivity[0].edge, Edge::kEdge);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

// §9.4.2: "Non-virtual methods of an object and built-in methods or system
// functions for an aggregate type are allowed in event control expressions
// as long as ... the method is defined as a function, not a task." A task
// call in an event expression is therefore illegal.
TEST(EventControlElaboration, TaskCallInEventExpressionRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t; endtask\n"
      "  initial @(t()) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(EventControlElaboration, TaskCallInAlwaysSensitivityRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic q;\n"
      "  task t; endtask\n"
      "  always @(t()) q = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(EventControlElaboration, TaskCallInIffGuardRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  task t; endtask\n"
      "  initial @(posedge clk iff t()) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §9.4.2: "Event expressions shall return singular values." A bare
// reference to an unpacked array — an aggregate type that does not reduce
// to a singular value — must be rejected at elaboration.
TEST(EventControlElaboration, UnpackedArrayEventExpressionRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr[3];\n"
      "  initial @(arr) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §9.4.2: An unpacked struct in an event expression also fails the
// singular-value requirement.
TEST(EventControlElaboration, UnpackedStructEventExpressionRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  struct { int a; int b; } s;\n"
      "  initial @(s) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §9.4.2: A packed struct reduces to a singular value and remains a
// legal event expression.
TEST(EventControlElaboration, PackedStructEventExpressionAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  struct packed { logic a; logic b; } s;\n"
      "  initial @(s) ;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §9.4.2: Sensitivity-list event expressions must also be singular.
TEST(EventControlElaboration, UnpackedArrayInAlwaysSensitivityRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr[3];\n"
      "  logic q;\n"
      "  always @(arr) q = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(EventControlElaboration, FunctionCallInEventExpressionAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function bit f; return 1; endfunction\n"
      "  initial @(f()) ;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §9.4.2 R16: "...allowed in event control expressions as long as the type
// of the return value is singular...". A function whose declared return
// type is an unpacked struct does not reduce to a singular value and must
// be rejected when called inside an event expression.
TEST(EventControlElaboration,
     FunctionReturningUnpackedStructInEventExpressionRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function struct { int a; int b; } f;\n"
      "    f.a = 0;\n"
      "  endfunction\n"
      "  initial @(f()) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace



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

// §9.4.2: an aggregate object may appear in an event expression when the
// expression reduces to a singular value. Selecting a singular member of an
// otherwise non-singular unpacked struct is accepted (contrast @(s), which is
// rejected because the whole struct is non-singular).
TEST(EventControlElaboration, UnpackedStructMemberEventExpressionAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  struct { int a; int b; } s;\n"
      "  initial @(s.a) ;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
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

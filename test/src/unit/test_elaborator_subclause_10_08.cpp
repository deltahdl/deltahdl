#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(AssignmentLikeContext, ProceduralAssignmentTypesStructLiteralFromLHS) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
             "  ab_t s;\n"
             "  initial s = '{8'h11, 8'h22};\n"
             "endmodule\n"));
}

TEST(AssignmentLikeContext, ContinuousAssignmentTypesStructLiteralFromLHS) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
             "  ab_t s;\n"
             "  assign s = '{8'h11, 8'h22};\n"
             "endmodule\n"));
}

TEST(AssignmentLikeContext, ExplicitTypedParameterDefaultIsAssignmentLike) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
             "  parameter ab_t P = '{8'h11, 8'h22};\n"
             "endmodule\n"));
}

TEST(AssignmentLikeContext, InputPortConnectionTypesStructLiteralFromPort) {
  EXPECT_TRUE(
      ElabOk("module inner(input struct packed {\n"
             "  logic [7:0] a; logic [7:0] b;\n"
             "} p);\n"
             "endmodule\n"
             "module t;\n"
             "  inner u(.p('{8'h11, 8'h22}));\n"
             "endmodule\n"));
}

TEST(AssignmentLikeContext, SubroutineInputArgTypesStructLiteralFromFormal) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
             "  task consume(input ab_t s);\n"
             "  endtask\n"
             "  initial consume('{8'h11, 8'h22});\n"
             "endmodule\n"));
}

TEST(AssignmentLikeContext, InoutPortVariableConnectionRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module sub(inout wire [7:0] p);\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] v;\n"
      "  sub u(.p(v));\n"
      "endmodule\n",
      f);
  // The rule that fires is §23.3.3.3, which forbids a variable on an inout port
  // declared with a net type, rather than anything in §10.8.
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "variable 'v' cannot be connected to inout port 'p'", 5, "23.3.3.3"));
}

TEST(AssignmentLikeContext, RefPortNetBindingRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module sub(ref logic [7:0] p);\n"
      "endmodule\n"
      "module top;\n"
      "  wire [7:0] w;\n"
      "  sub u(.p(w));\n"
      "endmodule\n",
      f);
  // The rule that fires is §23.3.3.2, which requires a variable on a ref port,
  // rather than anything in §10.8.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "net 'w' cannot be connected to ref port 'p'", 5,
                            "23.3.3.2"));
}

}  // namespace

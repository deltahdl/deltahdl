#include <gtest/gtest.h>

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

// §10.8 with §6.18: a port declared through a typedef has the type the
// typedef names, so a bare pattern on an input port of a structure typedef
// takes its type from the port as it does from the structure written out.
TEST(AssignmentLikeContext, InputPortConnectionTypesPatternFromStructTypedef) {
  EXPECT_TRUE(
      ElabOk("typedef struct { logic [7:0] a; logic [7:0] b; } pair_t;\n"
             "module inner(input pair_t p);\n"
             "endmodule\n"
             "module t;\n"
             "  inner u(.p('{8'h11, 8'h22}));\n"
             "endmodule\n"));
}

// §10.8 with §6.18: a typedef carries its unpacked dimensions into the type it
// names, so an input port of an array typedef is an unpacked array the
// pattern takes its type from, though the port writes no dimension itself.
TEST(AssignmentLikeContext, InputPortConnectionTypesPatternFromArrayTypedef) {
  EXPECT_TRUE(
      ElabOk("typedef logic [7:0] arr_t [2];\n"
             "module inner(input arr_t q);\n"
             "endmodule\n"
             "module t;\n"
             "  inner u(.q('{8'h33, 8'h44}));\n"
             "endmodule\n"));
}

// §6.18: a typedef renaming an array typedef names the same array, so the
// dimensions written further along the chain make the port an array too.
TEST(AssignmentLikeContext,
     InputPortConnectionTypesPatternThroughTypedefChain) {
  EXPECT_TRUE(
      ElabOk("typedef logic [7:0] arr_t [2];\n"
             "typedef arr_t arr2_t;\n"
             "module inner(input arr2_t q);\n"
             "endmodule\n"
             "module t;\n"
             "  inner u(.q('{8'h55, 8'h66}));\n"
             "endmodule\n"));
}

// §10.8: a typedef of a type no pattern can target leaves the port one the
// pattern cannot be connected to.
TEST(AssignmentLikeContext, PatternOnPortOfScalarTypedefRejected) {
  ElabFixture f;
  ElaborateSrc(
      "typedef int int_t;\n"
      "module sub(input int_t a);\n"
      "endmodule\n"
      "module top;\n"
      "  sub u(.a('{42}));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "an assignment pattern cannot be connected to this port", 5, "10.8"));
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

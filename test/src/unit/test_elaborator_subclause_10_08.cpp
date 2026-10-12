#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <initializer_list>
#include <string_view>

#include "common/diagnostic.h"
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

// §10.8 with §10.9 and §7.4: a packed array is a type a pattern constructs,
// so an input port with a packed dimension, written on the port or carried by
// its typedef or by a typedef further along the chain, is one an untyped
// pattern takes its type from.
TEST(AssignmentLikeContext, InputPortConnectionTypesPatternFromPackedArray) {
  ElabFixture f;
  ElaborateSrc(
      "typedef logic [1:0][3:0] T;\n"
      "typedef logic [3:0] nib_t;\n"
      "typedef nib_t [1:0] pair_t;\n"
      "module sub(input logic [1:0][3:0] a, input T b, input pair_t c);\n"
      "endmodule\n"
      "module top;\n"
      "  sub u(.a('{4'h1, 4'h2}), .b('{4'h3, 4'h4}), .c('{4'h5, 4'h6}));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(
      f.diag.Diagnostics(),
      "an assignment pattern cannot be connected to this port", 7, "10.8"));
  EXPECT_FALSE(f.diag.HasErrors());
}

// §10.8 (printed pages 259-260): the default correspondence between a
// `default:` value and the elements it covers is no assignment-like context,
// so an untyped pattern there has no type, in a declaration, a procedural or
// a continuous assignment and a subroutine alike. A typed pattern has its own,
// and an index key's value is in such a context.
TEST(AssignmentLikeContext, UntypedPatternAsDefaultValueRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef int row_t [0:1];\n"
      "  int a [0:1][0:1] = '{default: '{default: 1}};\n"
      "  int b [0:1][0:1];\n"
      "  wire [7:0] w [0:1][0:1];\n"
      "  assign w = '{0: '{8'h1, 8'h2}, default: '{8'h3, 8'h4}};\n"
      "  initial b = '{default: row_t'{default: 2}};\n"
      "  function automatic void f();\n"
      "    b = '{0: '{3, 4}, default: '{5, 6}};\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  constexpr std::string_view kMessage =
      "an untyped assignment pattern cannot be the value of a default key";
  for (uint32_t line : {3u, 6u, 9u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, line, "10.8"));
  }
  EXPECT_EQ(std::ranges::count_if(
                f.diag.Diagnostics(),
                [&](const Diagnostic& d) { return d.message == kMessage; }),
            3);
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

// §10.8 counts a connection to an output port among the assignment-like
// contexts, and §10.9 lets a positional pattern of lvalues stand on the side
// being assigned; a keyed pattern, an item that is no lvalue, a formal that is
// no aggregate and an inout port each leave the pattern illegal.
TEST(AssignmentLikeContext, PatternOnAggregateOutputPort) {
  ElabFixture f;
  ElaborateSrc(
      "typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "typedef struct packed { logic [7:0] a; } one_t;\n"
      "module sub(output pair_t p); endmodule\n"
      "module io(inout pair_t p); endmodule\n"
      "module sc(output logic [15:0] p); endmodule\n"
      "module top;\n"
      "  logic [7:0] x, y; logic [15:0] z; one_t s;\n"
      "  sub u1(.p('{x, y}));\n"
      "  sub u2(.p('{z[15:8], s.a}));\n"
      "  sub u3(.p('{{x[3:0], y[3:0]}, y}));\n"
      "  sub u4(.p('{a: x, b: y}));\n"
      "  sub u5(.p('{8'h1, y}));\n"
      "  io u6(.p('{x, y}));\n"
      "  sc u7(.p('{x, y}));\n"
      "endmodule\n",
      f, "top");
  for (uint32_t line : {8u, 9u, 10u}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                               "an assignment pattern cannot be connected to "
                               "this port",
                               line, "10.8"));
  }
  for (uint32_t line : {11u, 12u, 13u, 14u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "an assignment pattern cannot be connected to "
                              "this port",
                              line, "10.8"));
  }
}

// §10.9: a typed pattern has a type of its own and is connected to a port as
// any expression is.
TEST(AssignmentLikeContext, TypedPatternOnInputPortAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "module sub(input pair_t p); endmodule\n"
      "module top;\n"
      "  sub u(.p(pair_t'{8'h56, 8'h78}));\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §10.8 counts the actual of an output argument among the assignment-like
// contexts, so a positional pattern of variables may be passed to one.
TEST(AssignmentLikeContext, PatternOnOutputArgumentAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "typedef struct { logic [7:0] a, b; } ab_t;\n"
      "module m;\n"
      "  task automatic t(output ab_t s); s = '{8'h1, 8'h2}; endtask\n"
      "  logic [7:0] x, y;\n"
      "  initial t('{x, y});\n"
      "  initial t('{x, 8'h5});\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "output argument 's' requires a variable", 5,
                             "13.5"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "output argument 's' requires a variable", 6,
                            "13.5"));
}

// §10.8 excludes passing to a ref argument from the assignment-like contexts,
// and §13.5.2 has a ref argument refer to a variable, so a pattern or any
// other expression that names no variable is reported there.
TEST(AssignmentLikeContext, NonVariableOnRefArgumentRejected) {
  ElabFixture f;
  ElaborateSrc(
      "typedef struct { logic [7:0] a, b; } ab_t;\n"
      "module m;\n"
      "  task automatic t(ref ab_t s); endtask\n"
      "  ab_t v;\n"
      "  initial t('{8'h1, 8'h2});\n"
      "  initial t(v);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "ref argument 's' of 't' requires a variable", 5,
                            "13.5.2"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "ref argument 's' of 't' requires a variable", 6,
                             "13.5.2"));
}

// §10.8: an explicitly typed class parameter's value and a class
// specialization's parameter override are assignment-like contexts, so a
// pattern there is constant when its items are, of a structure type as of an
// array type.
TEST(AssignmentLikeContext, PatternClassParameterValues) {
  ElabFixture f;
  ElaborateSrc(
      "typedef struct packed { logic [7:0] a, b; } ab_t;\n"
      "class C #(parameter ab_t P = '{8'h11, 8'h22}); endclass\n"
      "class D #(parameter int A[2] = '{1, 2}); endclass\n"
      "module t;\n"
      "  int x;\n"
      "  D #('{5, 6}) h;\n"
      "  D #('{x, 6}) g;\n"
      "endmodule\n",
      f, "t");
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), "is not a constant", 2, "6.20.2"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "parameter override is not a constant expression",
                             6, "23.10.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parameter override is not a constant expression",
                            7, "23.10.2"));
}

}  // namespace

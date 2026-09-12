#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

// Annex D.3: $getpattern.
//
// "Use of this function is limited, however, it may only be used in a
// continuous assignment statement where the left-hand side is a concatenation
// of scalar nets and the argument to the system function is a memory element
// reference." The elaborator reports a call anywhere else under D.3: in a
// procedural statement, inside an expression of a continuous assignment's
// right-hand side, with a left-hand side that is no concatenation or holds an
// element that is no scalar net, or with an argument that names no memory
// element. The call in the placement the clause gives, D.3's own example
// reduced, elaborates clean.

namespace {

constexpr const char* kLimit =
    "$getpattern may only be used in a continuous assignment statement whose "
    "left-hand side is a concatenation of scalar nets";

// D.3's example, with three scalar inputs and two patterns.
TEST(GetpatternPlacement, TheExamplesPlacementIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [1:3] in_mem [1:2];\n"
      "  integer index;\n"
      "  wire i1, i2, i3;\n"
      "  assign {i1, i2, i3} = $getpattern(in_mem[index]);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// A call in a procedural statement, D.1's parser test having written one so.
TEST(GetpatternPlacement, ACallInAProceduralStatementIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [1:3] in_mem [1:2];\n"
      "  logic [1:3] x;\n"
      "  initial x = $getpattern(in_mem[1]);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      std::string(kLimit) + "; it is written in a procedural statement", 4,
      "D.3"));
}

// A call under a loop's body, which the walk reaches through the statement's
// child links, and under an operator, which it reaches through the
// expression's.
TEST(GetpatternPlacement, ACallNestedInAProceduralStatementIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [1:3] in_mem [1:2];\n"
      "  logic [1:3] x;\n"
      "  initial begin\n"
      "    for (int i = 1; i <= 2; i++) x = ~$getpattern(in_mem[i]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      std::string(kLimit) + "; it is written in a procedural statement", 5,
      "D.3"));
}

// A call that is an operand of the right-hand side rather than the whole of
// it.
TEST(GetpatternPlacement, ACallInsideTheRightHandSideIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [1:3] in_mem [1:2];\n"
      "  wire i1, i2, i3;\n"
      "  assign {i1, i2, i3} = ~$getpattern(in_mem[1]);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            std::string(kLimit) +
                                "; it is written inside an expression rather "
                                "than as the whole right-hand side",
                            4, "D.3"));
}

// A left-hand side that is a vector net rather than a concatenation.
TEST(GetpatternPlacement, ALeftHandSideThatIsNoConcatenationIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [1:3] in_mem [1:2];\n"
      "  wire [1:3] i;\n"
      "  assign i = $getpattern(in_mem[1]);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      std::string(kLimit) + "; the left-hand side is no concatenation", 4,
      "D.3"));
}

// A concatenation holding a vector net and a variable: each element that is
// no scalar net is reported where it stands, and the scalar net between them
// is not.
TEST(GetpatternPlacement, AnElementThatIsNoScalarNetIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [1:3] in_mem [1:2];\n"
      "  wire [1:0] v;\n"
      "  wire s;\n"
      "  logic r;\n"
      "  assign {v,\n"
      "          s,\n"
      "          r} = $getpattern(in_mem[1]);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    std::string(kLimit) +
                        "; this element of the left-hand side is no scalar net",
                    6, "D.3"));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    std::string(kLimit) +
                        "; this element of the left-hand side is no scalar net",
                    8, "D.3"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(),
                    std::string(kLimit) +
                        "; this element of the left-hand side is no scalar net",
                    7, "D.3"));
}

// An argument that is a variable with no unpacked dimension, a select of one,
// and no argument at all: none is a memory element reference.
TEST(GetpatternPlacement, AnArgumentNamingNoMemoryElementIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [1:3] word;\n"
      "  wire i1, i2, i3, j1, j2, j3, k1, k2, k3;\n"
      "  assign {i1, i2, i3} = $getpattern(word);\n"
      "  assign {j1, j2, j3} = $getpattern(word[1]);\n"
      "  assign {k1, k2, k3} = $getpattern();\n"
      "endmodule\n",
      f);
  constexpr const char* kArg =
      "$getpattern takes a memory element reference as its argument, a select "
      "of a variable declared with an unpacked dimension";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kArg, 4, "D.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kArg, 5, "D.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kArg, 6, "D.3"));
}

}  // namespace

#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

constexpr const char* kLimit =
    "$getpattern may only be used in a continuous assignment statement whose "
    "left-hand side is a concatenation of scalar nets";

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

constexpr const char* kNoMemoryElement =
    "$getpattern takes a memory element reference as its argument, a select "
    "of a variable declared with an unpacked dimension";

constexpr const char* kNoScalarNet =
    "$getpattern may only be used in a continuous assignment statement whose "
    "left-hand side is a concatenation of scalar nets; this element of the "
    "left-hand side is no scalar net";
constexpr const char* kNoConcatenation =
    "$getpattern may only be used in a continuous assignment statement whose "
    "left-hand side is a concatenation of scalar nets; the left-hand side is "
    "no concatenation";
constexpr const char* kProcedural =
    "$getpattern may only be used in a continuous assignment statement whose "
    "left-hand side is a concatenation of scalar nets; it is written in a "
    "procedural statement";

TEST(GetpatternPlacement, DISABLED_TwoArgumentsAreRejectedBesideOneAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [1:3] m [1:2];\n"
      "  wire a, b, c, d, e, g;\n"
      "  assign {a, b, c} = $getpattern(m[1], m[2]);\n"
      "  assign {d, e, g} = $getpattern(m[1]);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "$getpattern", 4, "D.3"));
  EXPECT_FALSE(ErrorOnLine(f.diag.Diagnostics(), 5));
}

TEST(GetpatternPlacement, AWholeMemoryIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [1:3] m [1:2];\n"
      "  wire a, b, c;\n"
      "  assign {a, b, c} = $getpattern(m);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoMemoryElement, 4, "D.3"));
}

TEST(GetpatternPlacement, AnElementOfAMultidimensionalArrayIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [1:3] m [1:2][1:2];\n"
      "  wire a, b, c;\n"
      "  assign {a, b, c} = $getpattern(m[1][2]);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoMemoryElement, 4, "D.3"));
}

TEST(GetpatternPlacement, DISABLED_ASubarrayOrASliceIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [1:3] md [1:2][1:2];\n"
      "  logic [1:3] m [1:2];\n"
      "  wire a, b, c, d, e, g;\n"
      "  assign {a, b, c} = $getpattern(md[1]);\n"
      "  assign {d, e, g} = $getpattern(m[1:2]);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoMemoryElement, 5, "D.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoMemoryElement, 6, "D.3"));
}

TEST(GetpatternPlacement, ElementsOfRegBitAndDynamicMemoriesAreAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  reg [1:3] r [1:2];\n"
      "  bit [1:3] q [1:2];\n"
      "  logic [1:3] dyn [];\n"
      "  wire a, b, c, d, e, g, h, j, k;\n"
      "  assign {a, b, c} = $getpattern(r[1]);\n"
      "  assign {d, e, g} = $getpattern(q[1]);\n"
      "  assign {h, j, k} = $getpattern(dyn[1]);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(GetpatternPlacement, DISABLED_AnElementOfAnIntArrayIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int m [1:2];\n"
      "  wire a, b;\n"
      "  assign {a, b} = $getpattern(m[1]);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoMemoryElement, 4, "D.3"));
}

TEST(GetpatternPlacement, DISABLED_AMemoryDeclaredOutsideTheModuleIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "logic [1:3] um [1:2];\n"
      "package p;\n"
      "  logic [1:3] pm [1:2];\n"
      "endpackage\n"
      "module s;\n"
      "  logic [1:3] sm [1:2];\n"
      "endmodule\n"
      "module top;\n"
      "  logic [1:3] m [1:2];\n"
      "  s s();\n"
      "  wire a, b, c, d, e, g, h, j, k;\n"
      "  assign {a, b, c} = $getpattern(um[1]);\n"
      "  assign {d, e, g} = $getpattern(p::pm[1]);\n"
      "  assign {h, j, k} = $getpattern(s.sm[1]);\n"
      "  if (1) begin : blk\n"
      "    wire x, y, z;\n"
      "    assign {x, y, z} = $getpattern(m[1]);\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  for (int line : {12, 13, 14, 17}) {
    EXPECT_FALSE(
        ReportedError(f.diag.Diagnostics(), kNoMemoryElement, line, "D.3"))
        << line;
  }
}

TEST(GetpatternPlacement, OtherNetKindsPortNetsAndImplicitNetsAreAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top(output wire o);\n"
      "  logic [1:3] m [1:2];\n"
      "  uwire a;\n"
      "  tri b;\n"
      "  wand c;\n"
      "  supply0 d;\n"
      "  wor e;\n"
      "  assign {a, b, c} = $getpattern(m[1]);\n"
      "  assign {o, d, e} = $getpattern(m[2]);\n"
      "  assign {imp1, imp2, imp3} = $getpattern(m[1]);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(GetpatternPlacement, InAnInterfaceAndAProgramTheRuleHolds) {
  for (const char* unit : {"interface", "program"}) {
    std::string src = unit;
    src +=
        " u;\n"
        "  logic [1:3] m [1:2];\n"
        "  logic [1:3] x;\n"
        "  wire a, b, c, s;\n"
        "  assign {a, b, c} = $getpattern(m[1]);\n"
        "  assign s = $getpattern(m[2]);\n"
        "  initial x = $getpattern(m[1]);\n"
        "end";
    src += unit;
    src +=
        "\n"
        "module top;\n"
        "  u i();\n"
        "endmodule\n";
    ElabFixture f;
    ElaborateSrc(src, f, "top");
    EXPECT_FALSE(ErrorOnLine(f.diag.Diagnostics(), 5)) << unit;
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoConcatenation, 6, "D.3"))
        << unit;
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kProcedural, 7, "D.3"))
        << unit;
  }
}

TEST(GetpatternPlacement, ACallInAnAlwaysOrAFinalProcedureIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [1:3] m [1:2];\n"
      "  logic [1:3] x, y;\n"
      "  logic clk;\n"
      "  always @(clk) x = $getpattern(m[1]);\n"
      "  final y = $getpattern(m[2]);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kProcedural, 5, "D.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kProcedural, 6, "D.3"));
}

TEST(GetpatternPlacement, DISABLED_ACallInAFunctionOrATaskBodyIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [1:3] m [1:2];\n"
      "  logic [1:3] x;\n"
      "  function automatic logic [1:3] fn();\n"
      "    return $getpattern(m[1]);\n"
      "  endfunction\n"
      "  task automatic tk();\n"
      "    x = $getpattern(m[2]);\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "$getpattern", 5, "D.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "$getpattern", 8, "D.3"));
}

TEST(GetpatternPlacement, ALoneScalarNetIsNoConcatenation) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [1:3] m [1:2];\n"
      "  wire s;\n"
      "  assign s = $getpattern(m[1]);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoConcatenation, 4, "D.3"));
}

TEST(GetpatternPlacement, DISABLED_ANetDeclarationAssignmentIsNoConcatenation) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [1:3] m [1:2];\n"
      "  wire [1:3] w = $getpattern(m[1]);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoConcatenation, 3, "D.3"));
}

TEST(GetpatternPlacement,
     VariablesSelectsAndNestedConcatenationsAreNoScalarNets) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [1:3] m [1:2];\n"
      "  logic [1:3] w [1:2];\n"
      "  logic r1, r2, r3;\n"
      "  wire [1:0] v;\n"
      "  wire s, t, u;\n"
      "  assign {r1, r2, r3} = $getpattern(m[1]);\n"
      "  assign {v[0],\n"
      "          s,\n"
      "          t} = $getpattern(m[2]);\n"
      "  assign {u,\n"
      "          {s, t}} = $getpattern(w[1]);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoScalarNet, 7, "D.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoScalarNet, 8, "D.3"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kNoScalarNet, 9, "D.3"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kNoScalarNet, 11, "D.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoScalarNet, 12, "D.3"));
}

TEST(GetpatternPlacement, DISABLED_AGenerateBlocksOwnScalarNetsAreAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [1:3] m [1:2];\n"
      "  wire [3:0] a;\n"
      "  if (1) begin : g\n"
      "    wire a, b, c;\n"
      "    assign {a, b, c} = $getpattern(m[1]);\n"
      "  end\n"
      "  case (1)\n"
      "    1: begin : h\n"
      "      wire a, b, c;\n"
      "      assign {a, b, c} = $getpattern(m[1]);\n"
      "    end\n"
      "  endcase\n"
      "  for (genvar i = 0; i < 2; i++) begin : l\n"
      "    wire a, b, c;\n"
      "    assign {a, b, c} = $getpattern(m[1]);\n"
      "  end\n"
      "endmodule\n",
      f);
  for (int line : {6, 11, 16}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kNoScalarNet, line, "D.3"))
        << line;
  }
}

TEST(GetpatternPlacement,
     DISABLED_AGenerateBlocksOwnNonScalarElementIsRejected) {
  const char* const kOuterNets[] = {"  wire b;\n", "  wire a, b;\n",
                                    "  wire a, b;\n"};
  const char* const kBlockA[] = {"    wire [3:0] a;\n", "    wire [3:0] a;\n",
                                 "    logic a;\n"};
  for (int k = 0; k < 3; ++k) {
    std::string src =
        "module top;\n"
        "  logic [1:3] m [1:2];\n";
    src += kOuterNets[k];
    src += "  if (1) begin : g\n";
    src += kBlockA[k];
    src += "    wire c;\n";
    src +=
        "    assign {a,\n"
        "            b,\n"
        "            c} = $getpattern(m[1]);\n"
        "  end\n"
        "endmodule\n";
    const uint32_t kFirst = LineHolding(src, "assign {a,");
    ElabFixture f;
    ElaborateSrc(src, f);
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kNoScalarNet, kFirst, "D.3"))
        << src;
    EXPECT_FALSE(
        ReportedError(f.diag.Diagnostics(), kNoScalarNet, kFirst + 1, "D.3"))
        << src;
    EXPECT_FALSE(
        ReportedError(f.diag.Diagnostics(), kNoScalarNet, kFirst + 2, "D.3"))
        << src;
  }
}

}  // namespace

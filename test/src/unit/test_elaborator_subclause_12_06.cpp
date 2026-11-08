#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(CaseMatchesElaboration, CaseMatchesWithGuardElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  logic guard;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    guard = 1'b1;\n"
      "    case(x) matches\n"
      "      8'd5 &&& guard: y = 8'd10;\n"
      "      default: y = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PatternMatching, RealLiteralPatternRejected) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  int y;\n"
      "  initial begin\n"
      "    r = 1.5;\n"
      "    case(r) matches\n"
      "      1.5: y = 1;\n"
      "      default: y = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "only an integral expression can serve as a constant expression pattern",
      7, "12.6"));
}

TEST(PatternMatching, RealLiteralPatternInMatchesOperatorRejected) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic y;\n"
      "  initial begin\n"
      "    r = 1.5;\n"
      "    y = r matches 2.5 ? 1 : 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "only an integral expression can serve as a constant expression pattern",
      6, "12.6"));
}

TEST(PatternMatching, StringLiteralPatternAgainstAStringValueRejected) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  string s;\n"
      "  logic y;\n"
      "  initial begin\n"
      "    s = \"hi\";\n"
      "    y = s matches \"hi\" ? 1 : 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a string value is matched with an integral "
                            "constant expression pattern",
                            6, "12.6"));
}

TEST(PatternMatching, StringLiteralPatternAgainstABitVectorAccepted) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [15:0] x;\n"
      "  initial if (x matches \"hi\") $display(\"hi\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PatternMatching, LocalparamIntegralPatternAccepted) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  localparam int P = 5;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    case(x) matches\n"
      "      P: y = 8'd1;\n"
      "      default: y = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PatternMatching, ParameterIntegralPatternAccepted) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t #(parameter int Q = 6);\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd6;\n"
      "    case(x) matches\n"
      "      Q: y = 8'd1;\n"
      "      default: y = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PatternMatching, ConstFunctionCallIntegralPatternAccepted) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  function automatic int cf(); return 5; endfunction\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    case(x) matches\n"
      "      cf(): y = 8'd1;\n"
      "      default: y = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PatternMatching, IntegerLiteralPatternAccepted) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    case(x) matches\n"
      "      8'd5: y = 8'd1;\n"
      "      8'd6: y = 8'd2;\n"
      "      default: y = 8'd0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PatternMatching, DuplicatePatternIdentifierRejected) {
  SimFixture f;
  ElaborateSrc(
      "typedef union tagged { struct { bit [3:0] a, b; } Add; } u_t;\n"
      "module t;\n"
      "  u_t u;\n"
      "  int y;\n"
      "  initial\n"
      "    case (u) matches\n"
      "      tagged Add '{.r1, .r1}: y = 1;\n"
      "      default: y = 0;\n"
      "    endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pattern identifier 'r1' is used more than once in "
                            "a single pattern",
                            7, "12.6"));
}

TEST(PatternMatching, DistinctPatternIdentifiersAccepted) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "typedef union tagged { struct { bit [3:0] a, b; } Add; } u_t;\n"
      "module t;\n"
      "  u_t u;\n"
      "  int y;\n"
      "  initial\n"
      "    case (u) matches\n"
      "      tagged Add '{.r1, .r2}: y = 1;\n"
      "      default: y = 0;\n"
      "    endcase\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PatternMatching, DuplicatePatternIdentifierInMatchesOperatorRejected) {
  SimFixture f;
  ElaborateSrc(
      "typedef union tagged { struct { bit [3:0] a, b; } Add; } u_t;\n"
      "module t;\n"
      "  u_t u;\n"
      "  logic y;\n"
      "  initial y = u matches (tagged Add '{.r1, .r1}) ? 1 : 0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pattern identifier 'r1' is used more than once in "
                            "a single pattern",
                            5, "12.6"));
}

TEST(PatternMatching, RealLiteralPatternNames12_6) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  int y;\n"
      "  initial begin\n"
      "    r = 1.5;\n"
      "    case(r) matches\n"
      "      1.5: y = 1;\n"
      "      default: y = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "only an integral expression can serve as a constant expression pattern",
      7, "12.6"));
}

TEST(PatternMatching, ARealLiteralPatternInAForInitializerIsReported) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic y;\n"
      "  integer i;\n"
      "  initial for (y = r matches 2.5 ? 1 : 0; i < 2; i = i + 1) begin end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "only an integral expression can serve as a constant expression pattern",
      5, "12.6"));
}

TEST(PatternMatching, ARealLiteralPatternInAForStepIsReported) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic y;\n"
      "  integer i;\n"
      "  initial for (i = 0; i < 2; y = r matches 2.5 ? 1 : 0) begin end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "only an integral expression can serve as a constant expression pattern",
      5, "12.6"));
}

TEST(PatternMatching, ARealLiteralPatternInAnAssertionPassStatementIsReported) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic y;\n"
      "  logic ok;\n"
      "  initial assert (ok) y = r matches 2.5 ? 1 : 0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "only an integral expression can serve as a constant expression pattern",
      5, "12.6"));
}

TEST(PatternMatching, ARealLiteralPatternInAnAssertionFailStatementIsReported) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic y;\n"
      "  logic ok;\n"
      "  initial assert (ok) else y = r matches 2.5 ? 1 : 0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "only an integral expression can serve as a constant expression pattern",
      5, "12.6"));
}

TEST(PatternMatching, ARealLiteralPatternInARandsequenceCodeBlockIsReported) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic y;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { y = r matches 2.5 ? 1 : 0; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "only an integral expression can serve as a constant expression pattern",
      6, "12.6"));
}

TEST(PatternMatching,
     ARealLiteralPatternInARandsequenceWeightCodeBlockIsReported) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  logic y;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : alt := 1 { y = r matches 2.5 ? 1 : 0; };\n"
      "      alt : { i = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "only an integral expression can serve as a constant expression pattern",
      7, "12.6"));
}

constexpr const char* kTaggedUnion =
    "  typedef union tagged {\n"
    "    struct { bit [3:0] val1, val2; } a;\n"
    "    struct { bit [7:0] val1, val2; } b;\n"
    "  } u;\n"
    "  u tmp;\n";

TEST(PatternVariableReads, ACaseMatchesItemReadsTheVariablesItsPatternBinds) {
  SimFixture f;
  ElaborateSrc(std::string("module t;\n") + kTaggedUnion +
                   "  initial case (tmp) matches\n"
                   "    tagged a '{.v, 0} : $display(\"a %d\", v);\n"
                   "    tagged a '{.v1, .v2} : $display(\"a %d %d\", v1, v2);\n"
                   "    tagged b '{0, .v} : $display(\"b %d\", v);\n"
                   "  endcase\n"
                   "endmodule\n",
               f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PatternVariableReads, AFilteredCaseMatchesItemReadsItsVariable) {
  SimFixture f;
  ElaborateSrc(std::string("module t;\n") + kTaggedUnion +
                   "  int y;\n"
                   "  initial case (tmp) matches\n"
                   "    tagged a '{.v, 0} &&& v > 2 : y = v;\n"
                   "    default : y = 0;\n"
                   "  endcase\n"
                   "endmodule\n",
               f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PatternVariableReads, AnIfMatchesBranchReadsTheVariableItsPatternBinds) {
  SimFixture f;
  ElaborateSrc(std::string("module t;\n") + kTaggedUnion +
                   "  initial if (tmp matches tagged a '{4'b01zx, .v})\n"
                   "    $display(\"a %d\", v);\n"
                   "endmodule\n",
               f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PatternVariableReads,
     AConditionalOperatorReadsTheVariableItsPatternBinds) {
  SimFixture f;
  ElaborateSrc(std::string("module t;\n") + kTaggedUnion +
                   "  bit [3:0] val;\n"
                   "  initial val = tmp matches tagged a '{.v, 0} ? v : 2;\n"
                   "endmodule\n",
               f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PatternVariableReads, ANameNoPatternBindsIsStillReported) {
  SimFixture f;
  ElaborateSrc(std::string("module t;\n") + kTaggedUnion +
                   "  initial case (tmp) matches\n"
                   "    tagged a '{.v, 0} : $display(\"a %d %d\", v, w);\n"
                   "  endcase\n"
                   "endmodule\n",
               f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'w'", 8,
                            "23.9"));
}

TEST(PatternVariableReads, TheWildcardPatternIsNoRead) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
      "  VInt v; logic flag; int x;\n"
      "  initial begin\n"
      "    if (v matches tagged Valid .* &&& flag) x = 1;\n"
      "    if (v matches tagged Valid .*) x = 2;\n"
      "    x = v matches tagged Valid .* &&& flag ? 3 : 4;\n"
      "    x = v matches tagged Valid .* ? 5 : 6;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PatternVariableReads, TheWildcardPatternInAClassMethodIsNoRead) {
  SimFixture f;
  ElaborateSrc(
      "class C;\n"
      "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
      "  function int f(VInt v, logic flag);\n"
      "    if (v matches tagged Valid .* &&& flag) return 1;\n"
      "    return v matches tagged Valid .* ? 2 : 3;\n"
      "  endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PatternMatching, TaggedPatternsCheckedAgainstTheTaggedUnion) {
  SimFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
      "  VInt v; int i;\n"
      "  initial begin\n"
      "    if (v matches tagged Bogus .x) ;\n"
      "    if (i matches tagged Valid .n) ;\n"
      "    if (v matches tagged Invalid .y) ;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "tagged pattern names 'Bogus', which is not a "
                            "member of the tagged union",
                            5, "12.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "tagged pattern is matched against a value that is "
                            "not a tagged union",
                            6, "12.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "tagged pattern for void member 'Invalid' has a "
                            "member pattern",
                            7, "12.6"));
}

TEST(PatternMatching, TaggedPatternsFittingTheTaggedUnionAccepted) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
      "  VInt v; int y;\n"
      "  function VInt get(); return v; endfunction\n"
      "  initial begin\n"
      "    if (v matches tagged Valid .n) y = n;\n"
      "    if (get() matches tagged Valid .m) y = m;\n"
      "    case (v) matches\n"
      "      tagged Invalid : y = 0;\n"
      "      tagged Valid .k : y = k;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PatternMatching, NestedPatternsCheckedAgainstTheMemberType) {
  SimFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef union tagged {\n"
      "    struct { bit [4:0] r1, r2; } Add;\n"
      "    union tagged {\n"
      "      bit [9:0] JmpU;\n"
      "      struct { bit [1:0] cc; bit [9:0] addr; } JmpC;\n"
      "    } Jmp;\n"
      "  } Instr;\n"
      "  Instr instr;\n"
      "  initial case (instr) matches\n"
      "    tagged Add '{.r1, .r2} : ;\n"
      "    tagged Jmp (tagged JmpC '{cc:.c, addr:.a}) : ;\n"
      "    tagged Jmp (tagged JmpX .a) : ;\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "tagged pattern names 'JmpX', which is not a "
                            "member of the tagged union",
                            13, "12.6"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

TEST(PatternMatching, StructurePatternsCheckedAgainstTheStructure) {
  SimFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct { int a; int b; } S;\n"
      "  S s;\n"
      "  initial begin\n"
      "    if (s matches '{foo: .x}) ;\n"
      "    if (s matches '{.x}) ;\n"
      "    if (s matches '{.x, .y, .z}) ;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "structure pattern names 'foo', which is not a "
                            "member of the structure",
                            5, "12.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "structure pattern lists 1 element(s) but the "
                            "structure has 2 member(s)",
                            6, "12.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "structure pattern lists 3 element(s) but the "
                            "structure has 2 member(s)",
                            7, "12.6"));
}

TEST(PatternMatching, StructurePatternsFittingTheStructureAccepted) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef struct { int a; int b; } S;\n"
      "  S s; int y;\n"
      "  function S gets(); return s; endfunction\n"
      "  initial begin\n"
      "    if (s matches '{a: .x}) y = x;\n"
      "    if (gets() matches '{.p, .q}) y = p;\n"
      "    if (s matches '{.x, .y2}) y = y2;\n"
      "    if (s.b matches 3) y = 3;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PatternMatching, StructurePatternAgainstANonStructureValueRejected) {
  SimFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct { int a; logic [3:0] b; } S;\n"
      "  typedef struct { S inner; int k; } T;\n"
      "  int x;\n"
      "  logic [7:0] v;\n"
      "  T t;\n"
      "  initial begin\n"
      "    if (x matches '{1, 2}) ;\n"
      "    if (v matches '{.p, .q}) ;\n"
      "    if (t matches '{'{1, 2}, '{3}}) ;\n"
      "    if (t matches '{inner: '{.p, .q}}) ;\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {8u, 9u, 10u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "structure pattern is matched against a value "
                              "that is not a structure",
                              line, "12.6"))
        << "line " << line;
  }
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

TEST(PatternMatching, VariableAsAConstantPatternRejected) {
  SimFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int a, b;\n"
      "  initial if (a matches b) $display(\"same\");\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "constant expression pattern is not a constant "
                            "expression",
                            3, "12.6"));
}

TEST(PatternMatching, ConstantPatternsAccepted) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int P = 4;\n"
      "  localparam [3:0] W = 2.5;\n"
      "  int a;\n"
      "  initial begin\n"
      "    if (a matches 5) ;\n"
      "    if (a matches P) ;\n"
      "    if (a matches P + 1) ;\n"
      "    if (a matches W) ;\n"
      "    if (a matches (P | 1)) ;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PatternMatching, NonIntegralConstantExpressionPatternsRejected) {
  SimFixture f;
  ElaborateSrc(
      "module m;\n"
      "  localparam real R = 1.5;\n"
      "  localparam string T = \"ab\";\n"
      "  localparam U = 2.5;\n"
      "  int i;\n"
      "  initial begin\n"
      "    if (i matches R) ;\n"
      "    if (i matches 1.5 * 2) ;\n"
      "    if (i matches T) ;\n"
      "    if (i matches U) ;\n"
      "  end\n"
      "endmodule\n",
      f);
  const char* msg =
      "only an integral expression can serve as a constant expression pattern";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), msg, 7, "12.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), msg, 8, "12.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), msg, 9, "12.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), msg, 10, "12.6"));
}

TEST(PatternMatching, IntegralParameterPatternAgainstARealValueRejected) {
  SimFixture f;
  ElaborateSrc(
      "module m;\n"
      "  localparam int P = 1;\n"
      "  real r;\n"
      "  initial begin\n"
      "    if (r matches P) ;\n"
      "    case (r) matches\n"
      "      P : ;\n"
      "      default : ;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pattern-matching if predicate value type differs "
                            "from the type of its integral pattern",
                            5, "12.6.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pattern-matching case selector type differs from "
                            "the type of its integral pattern",
                            6, "12.6.1"));
}

TEST(PatternMatching, PatternRulesHoldInAMethodOfAUnitClass) {
  SimFixture f;
  ElaborateSrc(
      "class C;\n"
      "  typedef struct { int a; int b; } S;\n"
      "  function void f(S s);\n"
      "    if (s matches '{.a, .a}) ;\n"
      "    if (s.a matches 1.5) ;\n"
      "  endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pattern identifier 'a' is used more than once in "
                            "a single pattern",
                            4, "12.6"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "only an integral expression can serve as a constant expression pattern",
      5, "12.6"));
}

TEST(PatternMatching, PatternRulesHoldInAMethodOfAModuleClass) {
  SimFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class C;\n"
      "    int k;\n"
      "    localparam int K2 = 1;\n"
      "    function void f(int i);\n"
      "      if (i matches 1.5) ;\n"
      "      if (i matches k) ;\n"
      "      if (i matches K2) ;\n"
      "    endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "only an integral expression can serve as a constant expression pattern",
      6, "12.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "constant expression pattern is not a constant "
                            "expression",
                            7, "12.6"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

}  // namespace

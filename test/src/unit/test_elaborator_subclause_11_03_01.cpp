#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(RealOps, CaseEqualityOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  logic eq;\n"
      "  initial eq = (a === b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '===' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, CaseInequalityOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  logic eq;\n"
      "  initial eq = (a !== b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '!==' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, WildcardEqualityOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  logic eq;\n"
      "  initial eq = (a ==? b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '==?' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, BitwiseAndOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  real c;\n"
      "  initial c = a & b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '&' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, BitwiseOrOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  real c;\n"
      "  initial c = a | b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '|' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, BitwiseXorOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  real c;\n"
      "  initial c = a ^ b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '^' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, BitwiseNegOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  real c;\n"
      "  initial c = ~a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unary operator '~' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, ShiftOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  real c;\n"
      "  initial c = a << 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '<<' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, ModulusOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  real c;\n"
      "  initial c = a % b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '%' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, LogicalAndOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  logic c;\n"
      "  initial c = a && b;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, RelationalOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  logic c;\n"
      "  initial c = a > b;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, ArithOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b, c;\n"
      "  initial c = a + b;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, LogicalEqualityOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  logic eq;\n"
      "  initial eq = (a == b);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, LogicalNegOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  logic c;\n"
      "  initial c = !a;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, UnaryPlusMinusOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b, c;\n"
      "  initial begin\n"
      "    b = +a;\n"
      "    c = -a;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, WildcardInequalityOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  logic eq;\n"
      "  initial eq = (a !=? b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '!=?' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, RightShiftOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  real c;\n"
      "  initial c = a >> 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '>>' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, ArithLeftShiftOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  real c;\n"
      "  initial c = a <<< 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '<<<' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, ArithRightShiftOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  real c;\n"
      "  initial c = a >>> 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '>>>' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, BitwiseXnorOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  real c;\n"
      "  initial c = a ~^ b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '~^' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, ReductionAndOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  logic c;\n"
      "  initial c = &a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unary operator '&' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, ReductionOrOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  logic c;\n"
      "  initial c = |a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unary operator '|' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, ReductionXorOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  logic c;\n"
      "  initial c = ^a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unary operator '^' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, ReductionNandOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  logic c;\n"
      "  initial c = ~&a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unary operator '~&' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, ReductionNorOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  logic c;\n"
      "  initial c = ~|a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unary operator '~|' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, ReductionXnorOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  logic c;\n"
      "  initial c = ~^a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unary operator '~^' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, ShortrealSubjectToSameRestrictions) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  shortreal a, b;\n"
      "  shortreal c;\n"
      "  initial c = a & b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '&' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, RealtimeSubjectToSameRestrictions) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  realtime a, b;\n"
      "  realtime c;\n"
      "  initial c = a & b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '&' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, LogicalOrOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  logic c;\n"
      "  initial c = a || b;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, ConditionalOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b, c;\n"
      "  logic sel;\n"
      "  initial c = sel ? a : b;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, PowerOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b, c;\n"
      "  initial c = a ** b;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, IllegalOpOnRealInContAssign) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  real c;\n"
      "  assign c = a & b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '&' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, LegalOpOnRealInContAssign) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  real c;\n"
      "  assign c = a + b;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, InsideOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  logic c;\n"
      "  initial c = a inside {1.0, 2.0, 3.0};\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, IncrementOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  initial begin a = 1.0; a++; end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, DecrementOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  initial begin a = 1.0; a--; end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, ImplicationOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  logic c;\n"
      "  initial c = a -> b;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, EquivalenceOnRealIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  logic c;\n"
      "  initial c = a <-> b;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, StructMemberRealAccessIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct { real realval; } S;\n"
      "  S s;\n"
      "  real v;\n"
      "  initial v = s.realval;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, RealArrayElementAccessIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real arr[4];\n"
      "  real v;\n"
      "  int i;\n"
      "  initial begin i = 0; v = arr[i]; end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, UnionMemberRealAccessIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef union { real realval; longint bits; } U;\n"
      "  U u;\n"
      "  real v;\n"
      "  initial v = u.realval;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RealOps, BitwiseXnorCaretTildeOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  real c;\n"
      "  initial c = a ^~ b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '^~' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, ReductionXnorCaretTildeOnRealIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a;\n"
      "  logic c;\n"
      "  initial c = ^~a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unary operator '^~' is not allowed on real operands", 4, "11.3.1"));
}

TEST(RealOps, BinaryXnorAndReductionXnorGiveDifferentReports) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real a, b;\n"
      "  real c;\n"
      "  logic d;\n"
      "  initial c = a ^~ b;\n"
      "  initial d = ^~a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '^~' is not allowed on real operands", 5, "11.3.1"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unary operator '^~' is not allowed on real operands", 6, "11.3.1"));
}

void ExpectIllegalOpOnRealIn(const std::string& stmt) {
  ElabFixture f;
  std::string src =
      "module m;\n"
      "  real a, b;\n"
      "  real c;\n"
      "  logic r;\n"
      "  initial\n"
      "    " +
      stmt + "\nendmodule\n";
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "binary operator '&' is not allowed on real "
                            "operands",
                            LineHolding(src, "a & b"), "11.3.1"));
}

TEST(RealOps, IllegalOpOnRealInAForkArm) {
  ExpectIllegalOpOnRealIn(
      "fork\n"
      "      c = a & b;\n"
      "    join");
}

TEST(RealOps, IllegalOpOnRealInAForInit) {
  ExpectIllegalOpOnRealIn("for (c = a & b; r == 0; r = 0) r = 1;");
}

TEST(RealOps, IllegalOpOnRealInAForStep) {
  ExpectIllegalOpOnRealIn("for (r = 0; r == 0; c = a & b) r = 1;");
}

TEST(RealOps, IllegalOpOnRealInAnAssertionPassStmt) {
  ExpectIllegalOpOnRealIn("assert (r) c = a & b;");
}

TEST(RealOps, IllegalOpOnRealInAnAssertionFailStmt) {
  ExpectIllegalOpOnRealIn("assert (r) else c = a & b;");
}

TEST(RealOps, IllegalOpOnRealInARandcaseItem) {
  ExpectIllegalOpOnRealIn("randcase 1: c = a & b; endcase");
}

TEST(RealOps, IllegalOpOnRealInARandsequenceCodeBlock) {
  ExpectIllegalOpOnRealIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : { c = a & b; };\n"
      "      endsequence\n"
      "    end");
}

TEST(RealOperandElaboration, IntegralOnlyAssignmentOperatorsOnRealReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real r;\n"
      "  initial begin\n"
      "    r %= 2;\n"
      "    r &= 1;\n"
      "    r |= 1;\n"
      "    r ^= 1;\n"
      "    r <<= 1;\n"
      "    r >>= 1;\n"
      "    r <<<= 1;\n"
      "    r >>>= 1;\n"
      "    r += 1.5;\n"
      "    r /= 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  const struct {
    const char* op;
    uint32_t line;
  } kWant[] = {{"'%='", 4},  {"'&='", 5},  {"'|='", 6},    {"'^='", 7},
               {"'<<='", 8}, {"'>>='", 9}, {"'<<<='", 10}, {"'>>>='", 11}};
  for (const auto& want : kWant) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              std::string("binary operator ") + want.op +
                                  " is not allowed on real operands",
                              want.line, "11.3.1"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 8u);
}

TEST(RealOperandElaboration, RealExpressionsOperandsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real r;\n"
      "  real ra [2];\n"
      "  int x;\n"
      "  initial begin\n"
      "    x = 2.5 % 2;\n"
      "    x = (r * 2.0) & 1;\n"
      "    x = ~1.5;\n"
      "    x = ra[0] << 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "binary operator '%' is not allowed on real "
                            "operands",
                            6, "11.3.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "binary operator '&' is not allowed on real "
                            "operands",
                            7, "11.3.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unary operator '~' is not allowed on real "
                            "operands",
                            8, "11.3.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "binary operator '<<' is not allowed on real "
                            "operands",
                            9, "11.3.1"));
}

TEST(RealOperandElaboration, RealOperatorRuleHeldInEveryScope) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real g;\n"
      "  int k = g % 2;\n"
      "  function int f(real a);\n"
      "    return a % 2;\n"
      "  endfunction\n"
      "  if (1) begin : b\n"
      "    initial k = g & 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {3u, 5u, 8u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "is not allowed on real operands", line,
                              "11.3.1"));
  }
}

TEST(RealOperandElaboration,
     DISABLED_RealOperandOfAConcatenationOrReplicationIsReported) {
  constexpr const char* kDecls =
      "  real r = 1.0; shortreal s; realtime tt; logic [7:0] a;\n"
      "  parameter real P = 1.5;\n"
      "  typedef struct { real rv; } st_t; st_t st;\n"
      "  logic [15:0] v;\n";
  for (const auto& [item, message] :
       {std::pair{"  wire [15:0] w = {r, a};\n", "concatenation"},
        std::pair{"  wire [15:0] w = {2{r}};\n", "replication"},
        std::pair{"  initial v = {s};\n", "concatenation"},
        std::pair{"  initial v = {tt, a};\n", "concatenation"},
        std::pair{"  initial v = {1.5, a};\n", "concatenation"},
        std::pair{"  initial v = {P, a};\n", "concatenation"},
        std::pair{"  initial v = {r + 1.0, a};\n", "concatenation"},
        std::pair{"  initial v = {st.rv, a};\n", "concatenation"},
        std::pair{"  initial {r, a} = 16'h0;\n", "concatenation"},
        std::pair{"  logic [15:0] d = {r, a};\n", "concatenation"},
        std::pair{"  function void f(); v = {r, a}; endfunction\n",
                  "concatenation"},
        std::pair{"  initial fork v = {2{r}}; join\n", "replication"}}) {
    const std::string kSrc =
        std::string("module t;\n") + kDecls + item + "endmodule\n";
    ElabFixture f;
    ElaborateSrc(kSrc, f);
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        std::string(message) + " is not allowed on real operands", 6, "11.3.1"))
        << kSrc;
  }
}

TEST(RealOperandElaboration,
     DISABLED_RealOperandOfAConcatenationInAClassMethodIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  real r; logic [7:0] a; logic [15:0] v;\n"
      "  function void f(); v = {r, a}; endfunction\n"
      "endclass\n"
      "module t; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "concatenation is not allowed on real operands", 3,
                            "11.3.1"));
}

TEST(RealOperandElaboration,
     IntegralConcatenationsAndRealArrayConcatenationsAreAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  real r = 1.0; logic [7:0] a; logic [15:0] v;\n"
      "  wire [15:0] w1 = {a, a};\n"
      "  wire [15:0] w2 = {2{a}};\n"
      "  real ra[2] = {r, 2.0};\n"
      "  real q[$];\n"
      "  initial begin q = {q, r}; v = {a, a}; end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace

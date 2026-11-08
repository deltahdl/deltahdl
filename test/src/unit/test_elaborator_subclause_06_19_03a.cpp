#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(Elaboration, EnumStrictTypeCheck_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  initial begin\n"
      "    e val;\n"
      "    val = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 5,
                            "6.19.3"));
}

TEST(Elaboration, EnumMemberAssign_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  initial begin\n"
      "    e val;\n"
      "    val = c;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, EnumCastAssign_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  initial begin\n"
      "    e val;\n"
      "    val = e'(2);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, EnumNonblockingIntAssign_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  e val;\n"
      "  always @(*) begin\n"
      "    val <= 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 5,
                            "6.19.3"));
}

TEST(Elaboration, EnumAlwaysCombIntAssign_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  e val;\n"
      "  always_comb val = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 4,
                            "6.19.3"));
}

TEST(Elaboration, EnumExprAssignNoCast_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  int x;\n"
      "  initial begin\n"
      "    e val;\n"
      "    val = x + 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 6,
                            "6.19.3"));
}

TEST(Elaboration, EnumCompoundAssign_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  initial begin\n"
      "    e val;\n"
      "    val += 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "compound assignment to enum variable without cast",
                            5, "6.19.4"));
}

TEST(Elaboration, EnumIncrement_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  initial begin\n"
      "    e val;\n"
      "    val++;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "increment/decrement of enum variable without cast",
                            5, "6.19.4"));
}

TEST(Elaboration, EnumLocalVarInitInt_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  initial begin\n"
      "    static e val = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 4,
                            "6.19.3"));
}

TEST(Elaboration, EnumModuleLevelInitInt_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  e val = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 3,
                            "6.19.3"));
}

TEST(Elaboration, EnumModuleLevelInitMember_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  e val = c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, EnumValueAssignedToInt_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  int y;\n"
      "  initial begin\n"
      "    e val;\n"
      "    val = c;\n"
      "    y = val;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, EnumAutoCastInIntExpr_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  int y;\n"
      "  initial begin\n"
      "    e val;\n"
      "    val = b;\n"
      "    y = val + 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, EnumArgIntWithoutCast_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  function automatic int g(e p);\n"
      "    return 0;\n"
      "  endfunction\n"
      "  int y;\n"
      "  initial begin\n"
      "    y = g(1);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "integer value passed to enum argument without cast", 8, "6.19.3"));
}

TEST(Elaboration, EnumArgMember_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  function automatic int g(e p);\n"
      "    return 0;\n"
      "  endfunction\n"
      "  int y;\n"
      "  initial begin\n"
      "    y = g(c);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, EnumArgCast_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  function automatic int g(e p);\n"
      "    return 0;\n"
      "  endfunction\n"
      "  int y;\n"
      "  initial begin\n"
      "    y = g(e'(1));\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, EnumUnionMemberDirectIntAssign_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  typedef union { e f; int i; } u_t;\n"
      "  u_t u;\n"
      "  initial begin\n"
      "    u.f = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, EnumRelationalCompareWithInt_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  int y;\n"
      "  initial begin\n"
      "    e val;\n"
      "    val = c;\n"
      "    if (1 == val) y = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, EnumSameTypeVarAssign_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  initial begin\n"
      "    e src;\n"
      "    e dst;\n"
      "    src = b;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, EnumDynamicCastAssign_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  initial begin\n"
      "    e val;\n"
      "    $cast(val, 2);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, EnumIntAssignInAForkArmIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  e val;\n"
      "  initial begin\n"
      "    fork\n"
      "      val = 1;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 6,
                            "6.19.3"));
}

TEST(Elaboration, EnumDeclaredAndAssignedInAForkArmIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  initial begin\n"
      "    fork\n"
      "      e val;\n"
      "      val = 1;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 6,
                            "6.19.3"));
}

TEST(Elaboration, EnumIntAssignInAForInitializationIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  e val;\n"
      "  int i;\n"
      "  initial begin\n"
      "    for (val = 1; i < 2; i = i + 1) ;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 6,
                            "6.19.3"));
}

TEST(Elaboration, EnumIntAssignInAForStepIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  e val;\n"
      "  int i;\n"
      "  initial begin\n"
      "    for (i = 0; i < 2; val = 1) ;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 6,
                            "6.19.3"));
}

TEST(Elaboration, EnumIntAssignInAnAssertionPassStmtIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  e val;\n"
      "  initial begin\n"
      "    assert (1) val = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 5,
                            "6.19.3"));
}

TEST(Elaboration, EnumDeclaredAndAssignedInAnAssertionPassStmtIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  initial begin\n"
      "    assert (1) begin\n"
      "      e val;\n"
      "      val = 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 6,
                            "6.19.3"));
}

TEST(Elaboration, EnumIntAssignInAnAssertionFailStmtIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  e val;\n"
      "  initial begin\n"
      "    assert (1) else val = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 5,
                            "6.19.3"));
}

TEST(Elaboration, EnumDeclaredAndAssignedInAnAssertionFailStmtIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  initial begin\n"
      "    assert (1) else begin\n"
      "      e val;\n"
      "      val = 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 6,
                            "6.19.3"));
}

TEST(Elaboration, EnumIntAssignInARandcaseItemIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  e val;\n"
      "  initial begin\n"
      "    randcase\n"
      "      1 : val = 1;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 6,
                            "6.19.3"));
}

TEST(Elaboration, EnumDeclaredAndAssignedInARandcaseItemIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  initial begin\n"
      "    randcase\n"
      "      1 : begin\n"
      "        e val;\n"
      "        val = 1;\n"
      "      end\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 7,
                            "6.19.3"));
}

TEST(Elaboration, EnumIntAssignInARandsequenceCodeBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  e val;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { val = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 6,
                            "6.19.3"));
}

TEST(Elaboration, EnumDeclaredAndAssignedInARandsequenceCodeBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { e val; val = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 5,
                            "6.19.3"));
}

TEST(Elaboration, EnumDeclaredInAForHeaderWithAnIntegerIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  initial\n"
      "    for (e val = 1; val != b; val = val + 1)\n"
      "      ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 4,
                            "6.19.3"));
}

TEST(Elaboration, AssignmentToAForHeaderEnumVariableIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  initial\n"
      "    for (e val = e'(1); val != b; val = val + 1)\n"
      "      ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 4,
                            "6.19.4"));
}

TEST(Elaboration, EnumDeclaredInAForHeaderWithACastIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  initial\n"
      "    for (e val = e'(1); val != b; val = c)\n"
      "      ;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, ScopedPackageEnumLiteralAssignedToItsTypeIsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  typedef enum { RED, GREEN, BLUE } color_t;\n"
      "endpackage\n"
      "module top();\n"
      "  import p::*;\n"
      "  color_t c = p::GREEN;\n"
      "  initial begin\n"
      "    static color_t d = p::RED;\n"
      "    c = p::BLUE;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, ScopedPackageParameterAssignedToEnumIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  typedef enum { RED, GREEN, BLUE } color_t;\n"
      "  parameter int K = 2;\n"
      "endpackage\n"
      "module top();\n"
      "  import p::*;\n"
      "  color_t c;\n"
      "  initial c = p::K;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 8,
                            "6.19.3"));
}

TEST(Elaboration, EnumArrayTakesAPatternOfEnumValues_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top();\n"
      "  typedef enum {ON, OFF} sw_e;\n"
      "  sw_e ea[3] = '{ON, OFF, ON};\n"
      "  sw_e ek[3] = '{default: OFF};\n"
      "  sw_e ed[2][2] = '{'{ON, OFF}, '{OFF, OFF}};\n"
      "  sw_e eb[2];\n"
      "  initial eb = '{OFF, ON};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, EnumArrayPatternOfIntegers_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {ON, OFF} sw_e;\n"
      "  sw_e ea[2] = '{0, 1};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 3,
                            "6.19.3"));
}

TEST(Elaboration, EnumAssignedFromAnotherEnumTypeRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef enum {red, green} Colors;\n"
      "  typedef enum {Mo, Tu} Week;\n"
      "  Colors c; Week w;\n"
      "  initial begin\n"
      "    w = Mo;\n"
      "    c = w;\n"
      "    c = Tu;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "value of enum type 'Week' assigned to enum "
                            "variable of type 'Colors' without cast",
                            7, "6.19.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "value of enum type 'Week' assigned to enum "
                            "variable of type 'Colors' without cast",
                            8, "6.19.3"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(Elaboration, EnumAssignedFromItsOwnTypeOrThroughACastAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef enum {red, green} Colors;\n"
             "  typedef Colors hue_t;\n"
             "  typedef enum {Mo, Tu} Week;\n"
             "  Colors c; hue_t h; Week w;\n"
             "  initial begin\n"
             "    c = h;\n"
             "    h = green;\n"
             "    c = Colors'(w);\n"
             "  end\n"
             "  initial begin\n"
             "    Week c;\n"
             "    c = w;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(Elaboration, NonEnumVariableAssignedToEnumIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef enum {A, B, C} e_t;\n"
      "  int i; real r; logic [1:0] l;\n"
      "  e_t v; e_t u;\n"
      "  e_t m = i;\n"
      "  initial begin\n"
      "    static e_t w = l;\n"
      "    v = i;\n"
      "    v = r;\n"
      "    v = u; v = B; v = e_t'(i);\n"
      "  end\n"
      "  initial begin\n"
      "    e_t i;\n"
      "    v = i;\n"
      "  end\n"
      "endmodule\n",
      f);
  for (auto [line, name] : {std::pair<uint32_t, const char*>{5u, "i"},
                            std::pair<uint32_t, const char*>{7u, "l"},
                            std::pair<uint32_t, const char*>{8u, "i"},
                            std::pair<uint32_t, const char*>{9u, "r"}}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              std::string("value of non-enum variable '") +
                                  name +
                                  "' assigned to enum variable without cast",
                              line, "6.19.3"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 4u);
}

TEST(Elaboration, EnumFunctionReturnWithoutCastIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef enum {A, B, C} e_t;\n"
      "  int i;\n"
      "  function e_t g; return 1; endfunction\n"
      "  function e_t h; return i; endfunction\n"
      "  function e_t k(e_t i); return i; endfunction\n"
      "  function e_t n; e_t i; i = B; return i; endfunction\n"
      "  function e_t p; return e_t'(i + 1); endfunction\n"
      "  function e_t q; return A; endfunction\n"
      "  function int r; return i; endfunction\n"
      "  function e_t z; return; endfunction\n"
      "  initial $display(g(), h(), k(A), n(), p(), q(), r(), z());\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer returned from enum function 'g' without "
                            "cast",
                            4, "6.19.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "value of non-enum variable 'i' returned from "
                            "enum function 'h' without cast",
                            5, "6.19.3"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "return statement in non-void function 'z' gives no value to return", 11,
      "12.8"));
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

}  // namespace

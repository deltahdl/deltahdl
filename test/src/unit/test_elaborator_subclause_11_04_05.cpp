#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(OperatorElaboration, LogicalEqualityElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial x = (8'd5 == 8'd5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, LogicalInequalityElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial x = (8'd5 != 8'd3);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, BinaryCaseEqElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial x = (8'd5 === 8'd5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, BinaryCaseNeqElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial x = (8'd5 !== 8'd3);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(EqualityOperatorElaboration, AlwaysCombEqualityCheck) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  logic y;\n"
      "  always_comb y = (a == b);\n"
      "  initial begin\n"
      "    a = 8'h42;\n"
      "    b = 8'h42;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(y, nullptr);

  EXPECT_EQ(y->value.ToUint64(), 1u);
}

TEST(EqualityOperatorElaboration, BlockingAssignComparisonOps) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, b;\n"
      "  int r_eq, r_ne, r_lt, r_gt, r_le, r_ge;\n"
      "  initial begin\n"
      "    a = 10;\n"
      "    b = 20;\n"
      "    r_eq = (a == b);\n"
      "    r_ne = (a != b);\n"
      "    r_lt = (a < b);\n"
      "    r_gt = (a > b);\n"
      "    r_le = (a <= b);\n"
      "    r_ge = (a >= b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* r_eq = f.ctx.FindVariable("r_eq");
  auto* r_ne = f.ctx.FindVariable("r_ne");
  auto* r_lt = f.ctx.FindVariable("r_lt");
  auto* r_gt = f.ctx.FindVariable("r_gt");
  auto* r_le = f.ctx.FindVariable("r_le");
  auto* r_ge = f.ctx.FindVariable("r_ge");
  ASSERT_NE(r_eq, nullptr);
  ASSERT_NE(r_ne, nullptr);
  ASSERT_NE(r_lt, nullptr);
  ASSERT_NE(r_gt, nullptr);
  ASSERT_NE(r_le, nullptr);
  ASSERT_NE(r_ge, nullptr);
  EXPECT_EQ(r_eq->value.ToUint64(), 0u);
  EXPECT_EQ(r_ne->value.ToUint64(), 1u);
  EXPECT_EQ(r_lt->value.ToUint64(), 1u);
  EXPECT_EQ(r_gt->value.ToUint64(), 0u);
  EXPECT_EQ(r_le->value.ToUint64(), 1u);
  EXPECT_EQ(r_ge->value.ToUint64(), 0u);
}

TEST(OperatorElaboration, ChandleEqualityWithNullElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  chandle h;\n"
      "  logic r;\n"
      "  initial r = (h == null);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, ChandleInequalityWithNullElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  chandle h;\n"
      "  logic r;\n"
      "  initial r = (h != null);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, ClassHandleEqualityWithNullElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C c;\n"
      "  logic r;\n"
      "  initial r = (c == null);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, ClassHandleCaseEqualityCompatibleElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class Base; endclass\n"
      "class Derived extends Base; endclass\n"
      "module m;\n"
      "  Base b;\n"
      "  Derived d;\n"
      "  logic r;\n"
      "  initial r = (b === d);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, ClassHandleEqualityIncompatibleRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class A; endclass\n"
      "class B; endclass\n"
      "module m;\n"
      "  A a;\n"
      "  B b;\n"
      "  logic r;\n"
      "  initial r = (a == b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "class handle comparison requires assignment compatible", 7, "11.4.5"));
}

TEST(OperatorElaboration, ChandleCaseEqualityWithNullElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  chandle h;\n"
      "  logic r;\n"
      "  initial r = (h === null);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, ClassHandleEqualitySameTypeElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  C b;\n"
      "  logic r;\n"
      "  initial r = (a == b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

void ExpectNonEquivalentAggregateCompareIn(const std::string& stmt) {
  ElabFixture f;
  std::string src =
      "module m;\n"
      "  typedef struct { logic [7:0] a; } s_t;\n"
      "  typedef struct { logic [15:0] b; } t_t;\n"
      "  s_t s;\n"
      "  t_t t;\n"
      "  logic r;\n"
      "  initial\n"
      "    " +
      stmt + "\nendmodule\n";
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "comparison of non-equivalent aggregate types 's_t' and 't_t'",
      LineHolding(src, "s == t"), "6.22.2"));
}

TEST(OperatorElaboration, NonEquivalentAggregateCompareInAForkArm) {
  ExpectNonEquivalentAggregateCompareIn(
      "fork\n"
      "      r = (s == t);\n"
      "    join");
}

TEST(OperatorElaboration, NonEquivalentAggregateCompareInAForInit) {
  ExpectNonEquivalentAggregateCompareIn(
      "for (r = (s == t); r == 0; r = 0) r = 1;");
}

TEST(OperatorElaboration, NonEquivalentAggregateCompareInAForStep) {
  ExpectNonEquivalentAggregateCompareIn(
      "for (r = 0; r == 0; r = (s == t)) r = 1;");
}

TEST(OperatorElaboration, NonEquivalentAggregateCompareInAnAssertionPassStmt) {
  ExpectNonEquivalentAggregateCompareIn("assert (r) r = (s == t);");
}

TEST(OperatorElaboration, NonEquivalentAggregateCompareInAnAssertionFailStmt) {
  ExpectNonEquivalentAggregateCompareIn("assert (r) else r = (s == t);");
}

TEST(OperatorElaboration, NonEquivalentAggregateCompareInARandcaseItem) {
  ExpectNonEquivalentAggregateCompareIn("randcase 1: r = (s == t); endcase");
}

TEST(OperatorElaboration,
     NonEquivalentAggregateCompareInARandsequenceCodeBlock) {
  ExpectNonEquivalentAggregateCompareIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : { r = (s == t); };\n"
      "      endsequence\n"
      "    end");
}

TEST(EqualityOperatorElaboration, ClassHandleComparedWithLiteralReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  class C; endclass\n"
      "  C h;\n"
      "  bit b;\n"
      "  initial begin\n"
      "    b = h == 5;\n"
      "    b = 1.5 != h;\n"
      "    b = h === \"a\";\n"
      "    b = h == '0;\n"
      "    b = h == null;\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {6u, 7u, 8u, 9u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "a class handle is compared only with a class "
                              "handle or null",
                              line, "11.4.5"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 4u);
}

TEST(EqualityOperatorElaboration,
     ClassHandleComparedWithIntegralValueReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  class C; endclass\n"
      "  C h, g;\n"
      "  int i; string s; typedef enum {A} e_t;\n"
      "  real r; function int fn(); return 0; endfunction\n"
      "  bit b;\n"
      "  initial begin\n"
      "    b = h == i;\n"
      "    b = h != i + 1;\n"
      "    b = -r == h;\n"
      "    b = h == null;\n"
      "    b = h == g;\n"
      "    b = h == s;\n"
      "    b = h == A;\n"
      "    b = h == fn();\n"
      "    b = h == s + 1;\n"
      "    b = h == 1 + s;\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {8u, 9u, 10u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "a class handle is compared only with a class "
                              "handle or null",
                              line, "11.4.5"));
  }
  for (uint32_t line : {11u, 12u, 13u, 14u, 15u, 16u, 17u}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                               "a class handle is compared only with a class "
                               "handle or null",
                               line, "11.4.5"));
  }
}

}  // namespace

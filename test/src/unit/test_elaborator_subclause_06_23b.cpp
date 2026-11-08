#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_generate_elab.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

int CountVarsEndingWith(const RtlirModule* mod, char last) {
  int count = 0;
  for (const auto& var : mod->variables) {
    if (!var.name.empty() && var.name.back() == last) ++count;
  }
  return count;
}

void ExpectBranchesTaken(const GenerateElab& r, std::string_view taken,
                         std::string_view skipped) {
  ASSERT_NE(r.design, nullptr);
  EXPECT_FALSE(r.f.has_errors);
  EXPECT_EQ(r.f.diag.WarningCount(), 0u);
  ASSERT_EQ(r.design->top_modules.size(), 1u);
  for (char c : taken) {
    EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], c), 1) << c;
  }
  for (char c : skipped) {
    EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], c), 0) << c;
  }
}

TEST(TypeOperatorElab, TypeOfThisInClassMethodAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  static function type(this) get();\n"
             "    return null;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(TypeOperatorElab, TypeRefComparedToIntegerLiteralRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m #(parameter type T = int) ();\n"
      "  initial begin\n"
      "    if (type(T) == 5) $stop;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type reference may be compared only with another type reference", 3,
      "6.23"));
}

TEST(TypeOperatorElab, TypeRefComparedToTypeRefAccepted) {
  EXPECT_TRUE(
      ElabOk("module m #(parameter type T = int) ();\n"
             "  initial begin\n"
             "    if (type(T) == type(int)) $stop;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(TypeOperatorElab, NonTypeRefSideOfCaseEqRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m #(parameter type T = int) ();\n"
      "  initial begin\n"
      "    if (type(T) === 0) $stop;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type reference may be compared only with another type reference", 3,
      "6.23"));
}

TEST(TypeOperatorElab, TypeRefComparedToVariableRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m #(parameter type T = int) ();\n"
      "  int v;\n"
      "  initial begin\n"
      "    if (type(T) != v) $stop;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type reference may be compared only with another type reference", 4,
      "6.23"));
}

TEST(TypeOperatorElab, NonTypeRefLeftOfCompareRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m #(parameter type T = int) ();\n"
      "  initial begin\n"
      "    if (7 == type(T)) $stop;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type reference may be compared only with another type reference", 3,
      "6.23"));
}

TEST(TypeOperatorElab, NonTypeRefBangEqRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m #(parameter type T = int) ();\n"
      "  initial begin\n"
      "    if (type(T) !== 0) $stop;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type reference may be compared only with another type reference", 3,
      "6.23"));
}

TEST(TypeOperatorElab, HierarchicalRefInTypeArgRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module sub;\n"
      "  int q;\n"
      "endmodule\n"
      "module m;\n"
      "  sub s();\n"
      "  var type(s.q) v;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "type operator argument uses a hierarchical reference, "
                    "which the type operator does not accept",
                    6, "6.23"));
}

TEST(TypeOperatorElab, HierarchicalRefInBinaryArgRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module sub;\n"
      "  int q;\n"
      "endmodule\n"
      "module m;\n"
      "  sub s();\n"
      "  var type(s.q + 1) v;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "type operator argument uses a hierarchical reference, "
                    "which the type operator does not accept",
                    6, "6.23"));
}

TEST(TypeOperatorElab, StructureMemberInTypeArgAccepted) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  typedef struct packed { bit [7:0] f; bit g; } st;\n"
             "  st p;\n"
             "  int d, e;\n"
             "  initial d = type(p.f)'(5);\n"
             "  initial e = type(d + p.f)'(5);\n"
             "endmodule\n"));
}

TEST(TypeOperatorElab, DynamicArrayElementInTypeArgRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int d[];\n"
      "  var type(d[0]) v;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type operator argument shall not reference elements of dynamic objects",
      3, "6.23"));
}

TEST(TypeOperatorElab, AssocArrayElementInTypeArgRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int a[string];\n"
      "  var type(a[\"k\"]) v;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type operator argument shall not reference elements of dynamic objects",
      3, "6.23"));
}

TEST(TypeOperatorElab, QueueElementInTypeArgRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "  var type(q[0]) v;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type operator argument shall not reference elements of dynamic objects",
      3, "6.23"));
}

TEST(TypeOperatorGenerate, EqualMatchingTypesSelectsThenBranch) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  parameter type T = int;\n"
      "  if (type(T) == type(int)) begin\n"
      "    logic a;\n"
      "  end else begin\n"
      "    logic b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  EXPECT_FALSE(r.f.has_errors);
  ASSERT_EQ(r.design->top_modules.size(), 1u);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'a'), 1);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'b'), 0);
}

TEST(TypeOperatorGenerate, CaseOverTypeReferencesSelectsTheMatchingItem) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  bit [12:0] A_bus;\n"
      "  real R1;\n"
      "  parameter type bus_t = type(A_bus);\n"
      "  parameter type rbus_t = type(R1);\n"
      "  case (type(bus_t))\n"
      "    type(bit[12:0]): begin logic a; end\n"
      "    type(real): begin logic b; end\n"
      "  endcase\n"
      "  case (type(rbus_t))\n"
      "    type(bit[12:0]): begin logic c; end\n"
      "    type(real): begin logic d; end\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  EXPECT_FALSE(r.f.has_errors);
  ASSERT_EQ(r.design->top_modules.size(), 1u);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'a'), 1);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'b'), 0);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'c'), 0);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'd'), 1);
}

TEST(TypeOperatorGenerate, CaseOverTypeReferencesFallsToTheDefault) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  parameter type T = bit [11:0];\n"
      "  case (type(T))\n"
      "    type(bit[12:0]), type(int): begin logic a; end\n"
      "    default: begin logic b; end\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  EXPECT_FALSE(r.f.has_errors);
  ASSERT_EQ(r.design->top_modules.size(), 1u);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'a'), 0);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'b'), 1);
}

TEST(TypeOperatorGenerate, EqualNonMatchingTypesSelectsElseBranch) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  parameter type T = int;\n"
      "  if (type(T) == type(real)) begin\n"
      "    logic a;\n"
      "  end else begin\n"
      "    logic b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  EXPECT_FALSE(r.f.has_errors);
  ASSERT_EQ(r.design->top_modules.size(), 1u);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'a'), 0);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'b'), 1);
}

TEST(TypeOperatorGenerate, EqualVectorsWithOtherBoundsSelectElseBranch) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  if (type(bit [7:0]) == type(bit [0:7])) begin\n"
      "    logic a;\n"
      "  end else begin\n"
      "    logic b;\n"
      "  end\n"
      "  if (type(bit [7:0]) == type(bit [7:0])) begin\n"
      "    logic c;\n"
      "  end else begin\n"
      "    logic d;\n"
      "  end\n"
      "endmodule\n");
  ExpectBranchesTaken(r, "bc", "ad");
}

TEST(TypeOperatorGenerate, DistinctAggregateTypedefsSelectElseBranch) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  typedef struct packed {int A; int B;} AB_t;\n"
      "  typedef struct packed {int A; int B;} otherAB_t;\n"
      "  typedef AB_t sameAB_t;\n"
      "  typedef enum {X, Y} e1_t;\n"
      "  typedef enum {P, Q} e2_t;\n"
      "  if (type(AB_t) == type(otherAB_t)) begin\n"
      "    logic a;\n"
      "  end else begin\n"
      "    logic b;\n"
      "  end\n"
      "  if (type(e1_t) == type(e2_t)) begin\n"
      "    logic c;\n"
      "  end else begin\n"
      "    logic d;\n"
      "  end\n"
      "  if (type(AB_t) == type(sameAB_t)) begin\n"
      "    logic e;\n"
      "  end else begin\n"
      "    logic f;\n"
      "  end\n"
      "endmodule\n");
  ExpectBranchesTaken(r, "bde", "acf");
}

TEST(TypeOperatorGenerate, ScopedTypedefsInTypeReferencesAreConstant) {
  auto r = RunGenerateElaboration(
      "package p;\n"
      "  typedef shortint t_s;\n"
      "endpackage\n"
      "module top;\n"
      "  class D;\n"
      "    typedef int t_i;\n"
      "  endclass\n"
      "  if (type(p::t_s) == type(shortint)) begin\n"
      "    logic a;\n"
      "  end else begin\n"
      "    logic b;\n"
      "  end\n"
      "  if (type(D::t_i) == type(int)) begin\n"
      "    logic c;\n"
      "  end else begin\n"
      "    logic d;\n"
      "  end\n"
      "  if (type(D::t_i) == type(p::t_s)) begin\n"
      "    logic e;\n"
      "  end else begin\n"
      "    logic f;\n"
      "  end\n"
      "endmodule\n");
  ExpectBranchesTaken(r, "acf", "bde");
}

TEST(TypeOperatorGenerate, SpecializedClassTypedefsInTypeReferences) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  class C #(parameter SIZE = 1);\n"
      "    typedef bit [SIZE-1:0] t_v;\n"
      "    typedef struct packed { bit [SIZE-1:0] m; } t_struct;\n"
      "  endclass\n"
      "  if (type(C#(4)::t_v) == type(bit [3:0])) begin\n"
      "    logic a;\n"
      "  end else begin\n"
      "    logic b;\n"
      "  end\n"
      "  if (type(C#(4)::t_v) == type(bit [7:0])) begin\n"
      "    logic c;\n"
      "  end else begin\n"
      "    logic d;\n"
      "  end\n"
      "  if (type(C#(4)::t_struct) == type(C#(8)::t_struct)) begin\n"
      "    logic e;\n"
      "  end else begin\n"
      "    logic f;\n"
      "  end\n"
      "  if (type(C#(4)::t_struct) == type(C#(4)::t_struct)) begin\n"
      "    logic g;\n"
      "  end else begin\n"
      "    logic h;\n"
      "  end\n"
      "endmodule\n");
  ExpectBranchesTaken(r, "adfg", "bceh");
}

TEST(TypeOperatorGenerate, NotEqualNonMatchingTypesSelectsThenBranch) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  parameter type T = int;\n"
      "  if (type(T) != type(real)) begin\n"
      "    logic a;\n"
      "  end else begin\n"
      "    logic b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  EXPECT_FALSE(r.f.has_errors);
  ASSERT_EQ(r.design->top_modules.size(), 1u);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'a'), 1);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'b'), 0);
}

TEST(TypeOperatorGenerate, CaseEqualMatchingTypesSelectsThenBranch) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  parameter type T = int;\n"
      "  if (type(T) === type(int)) begin\n"
      "    logic a;\n"
      "  end else begin\n"
      "    logic b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  EXPECT_FALSE(r.f.has_errors);
  ASSERT_EQ(r.design->top_modules.size(), 1u);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'a'), 1);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'b'), 0);
}

TEST(TypeOperatorGenerate, CaseNotEqualMatchingTypesSelectsElseBranch) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  parameter type T = int;\n"
      "  if (type(T) !== type(int)) begin\n"
      "    logic a;\n"
      "  end else begin\n"
      "    logic b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  EXPECT_FALSE(r.f.has_errors);
  ASSERT_EQ(r.design->top_modules.size(), 1u);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'a'), 0);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'b'), 1);
}

TEST(TypeOperatorGenerate, BuiltinDataTypeReferencesFoldByMatching) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  if (type(int) == type(bit)) begin\n"
      "    logic a;\n"
      "  end else begin\n"
      "    logic b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  EXPECT_FALSE(r.f.has_errors);
  ASSERT_EQ(r.design->top_modules.size(), 1u);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'a'), 0);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'b'), 1);
}

TEST(TypeOperatorGenerate, LocalparamTypeOperandFoldsByMatching) {
  auto r = RunGenerateElaboration(
      "module top;\n"
      "  localparam type T = int;\n"
      "  if (type(T) == type(int)) begin\n"
      "    logic a;\n"
      "  end else begin\n"
      "    logic b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  EXPECT_FALSE(r.f.has_errors);
  ASSERT_EQ(r.design->top_modules.size(), 1u);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'a'), 1);
  EXPECT_EQ(CountVarsEndingWith(r.design->top_modules[0], 'b'), 0);
}

constexpr const char* kFrameClass =
    "class Frame;\n"
    "  typedef byte payload_t;\n"
    "  typedef logic [7:0] beat_t;\n"
    "endclass\n";

TEST(TypeOperatorElab, ClassScopedTypedefVarDeclAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(std::string(kFrameClass) +
                                  "module m;\n"
                                  "  var type(Frame::payload_t) v;\n"
                                  "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirVariable* v = FindVar(design, "m", "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 8u);
  EXPECT_TRUE(v->is_signed);
}

TEST(TypeOperatorElab, ClassScopedTypedefNetDeclAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(std::string(kFrameClass) +
                                  "module m;\n"
                                  "  wire type(Frame::beat_t) w;\n"
                                  "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirNet* w = FindNet(design, "m", "w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->width, 8u);
  EXPECT_FALSE(w->is_signed);
}

TEST(TypeOperatorElab, InstanceMemberInTypeArgStillRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module sub;\n"
      "  int q;\n"
      "endmodule\n"
      "module m;\n"
      "  sub s();\n"
      "  var type(s.q) v;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "type operator argument uses a hierarchical reference, "
                    "which the type operator does not accept",
                    6, "6.23"));
}

TEST(TypeOperatorElab, MemberAccessOverScopeResolutionRejected) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module m;\n"
      "  var type(C::x.y) v;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "type operator argument uses a hierarchical reference, "
                    "which the type operator does not accept",
                    5, "6.23"));
}

TEST(TypeOperatorElab, ClassScopedTypedefAsTypeParamDefault) {
  ElabFixture f;
  auto* design =
      ElaborateSrc(std::string(kFrameClass) +
                       "module m;\n"
                       "  localparam type P = type(Frame::payload_t);\n"
                       "  P v;\n"
                       "endmodule\n",
                   f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirVariable* v = FindVar(design, "m", "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 8u);
  EXPECT_TRUE(v->is_signed);
}

void ExpectTypeRefComparedToLiteralIn(const std::string& stmt) {
  ElabFixture f;
  std::string src =
      "module m #(parameter type T = int) ();\n"
      "  logic r;\n"
      "  initial\n"
      "    " +
      stmt + "\nendmodule\n";
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type reference may be compared only with another type reference",
      LineHolding(src, "type(T) == 5"), "6.23"));
}

TEST(TypeOperatorElab, TypeRefComparedToLiteralInAForkArm) {
  ExpectTypeRefComparedToLiteralIn(
      "fork\n"
      "      r = (type(T) == 5);\n"
      "    join");
}

TEST(TypeOperatorElab, TypeRefComparedToLiteralInAForInit) {
  ExpectTypeRefComparedToLiteralIn(
      "for (r = (type(T) == 5); r == 0; r = 0) r = 1;");
}

TEST(TypeOperatorElab, TypeRefComparedToLiteralInAForStep) {
  ExpectTypeRefComparedToLiteralIn(
      "for (r = 0; r == 0; r = (type(T) == 5)) r = 1;");
}

TEST(TypeOperatorElab, TypeRefComparedToLiteralInAnAssertionPassStmt) {
  ExpectTypeRefComparedToLiteralIn("assert (r) r = (type(T) == 5);");
}

TEST(TypeOperatorElab, TypeRefComparedToLiteralInAnAssertionFailStmt) {
  ExpectTypeRefComparedToLiteralIn("assert (r) else r = (type(T) == 5);");
}

TEST(TypeOperatorElab, TypeRefComparedToLiteralInARandcaseItem) {
  ExpectTypeRefComparedToLiteralIn("randcase 1: r = (type(T) == 5); endcase");
}

TEST(TypeOperatorElab, TypeRefComparedToLiteralInARandsequenceCodeBlock) {
  ExpectTypeRefComparedToLiteralIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : { r = (type(T) == 5); };\n"
      "      endsequence\n"
      "    end");
}

void ExpectDynamicElementInTypeArgIn(const std::string& stmt) {
  ElabFixture f;
  std::string src =
      "module m;\n"
      "  int d[];\n"
      "  logic r;\n"
      "  initial\n"
      "    " +
      stmt + "\nendmodule\n";
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type operator argument shall not reference elements of dynamic objects",
      LineHolding(src, "type(d[0])"), "6.23"));
}

TEST(TypeOperatorElab, DynamicElementInTypeArgInAForkArm) {
  ExpectDynamicElementInTypeArgIn(
      "fork\n"
      "      r = (type(d[0]) == type(int));\n"
      "    join");
}

TEST(TypeOperatorElab, DynamicElementInTypeArgInAForInit) {
  ExpectDynamicElementInTypeArgIn(
      "for (r = (type(d[0]) == type(int)); r == 0; r = 0) r = 1;");
}

TEST(TypeOperatorElab, DynamicElementInTypeArgInAForStep) {
  ExpectDynamicElementInTypeArgIn(
      "for (r = 0; r == 0; r = (type(d[0]) == type(int))) r = 1;");
}

TEST(TypeOperatorElab, DynamicElementInTypeArgInAnAssertionPassStmt) {
  ExpectDynamicElementInTypeArgIn("assert (r) r = (type(d[0]) == type(int));");
}

TEST(TypeOperatorElab, DynamicElementInTypeArgInAnAssertionFailStmt) {
  ExpectDynamicElementInTypeArgIn(
      "assert (r) else r = (type(d[0]) == type(int));");
}

TEST(TypeOperatorElab, DynamicElementInTypeArgInARandcaseItem) {
  ExpectDynamicElementInTypeArgIn(
      "randcase 1: r = (type(d[0]) == type(int)); endcase");
}

TEST(TypeOperatorElab, DynamicElementInTypeArgInARandsequenceCodeBlock) {
  ExpectDynamicElementInTypeArgIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : { r = (type(d[0]) == type(int)); };\n"
      "      endsequence\n"
      "    end");
}

TEST(TypeOperatorElab, TypeParamSetToAPackedTypeReference) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam type T = type(bit [12:0]);\n"
      "  T tv;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirVariable* tv = FindVar(design, "m", "tv");
  ASSERT_NE(tv, nullptr);
  EXPECT_EQ(tv->width, 13u);
  EXPECT_FALSE(tv->is_signed);
}

TEST(TypeOperatorElab, TypeParamSetToAnExpressionTypeReference) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  bit [12:0] A_bus;\n"
      "  int n;\n"
      "  parameter type bus_t = type(A_bus);\n"
      "  localparam type int_t = type(n);\n"
      "  bus_t bv;\n"
      "  int_t iv;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirVariable* bv = FindVar(design, "m", "bv");
  ASSERT_NE(bv, nullptr);
  EXPECT_EQ(bv->width, 13u);
  EXPECT_FALSE(bv->is_signed);
  const RtlirVariable* iv = FindVar(design, "m", "iv");
  ASSERT_NE(iv, nullptr);
  EXPECT_EQ(iv->width, 32u);
  EXPECT_TRUE(iv->is_signed);
}

TEST(TypeOperatorElab, AnUndeclaredTypeReferenceArgumentIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  var type(nosuch) v;\n"
      "  initial begin\n"
      "    var type(missing) w;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'nosuch'", 2,
                            "23.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'missing'", 4,
                            "23.9"));
}

TEST(TypeOperatorElab, ADeclaredTypeReferenceArgumentIsNotReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef logic [3:0] n_t;\n"
      "  typedef enum {K0, K1} k_t;\n"
      "  int x;\n"
      "  var type(x) a;\n"
      "  var type(n_t) b;\n"
      "  var type(int) c;\n"
      "  var type(K1) e;\n"
      "  initial begin\n"
      "    int y;\n"
      "    var type(y) d;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace

#include "fixture_elaborator.h"
#include "helpers_generate_elab.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

// Counts variables in `mod` whose name ends in `last`. A declaration inside an
// (unnamed) generate block reaches the module's variable list under a scoped
// name, so the trailing character identifies which alternative was taken.
int CountVarsEndingWith(const RtlirModule* mod, char last) {
  int count = 0;
  for (const auto& var : mod->variables) {
    if (!var.name.empty() && var.name.back() == last) ++count;
  }
  return count;
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

// The §6.23 rule is symmetric: a non-type-reference operand is rejected
// whether it appears on the left or the right of the comparison.
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

// §6.23 — the prohibition extends to the bang-equal form.
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

// §6.23 — the inner expression of type(...) shall not contain a
// hierarchical reference. A member-access subtree is treated as a
// hierarchical reference here.
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type operator argument shall not contain a hierarchical reference", 6,
      "6.23"));
}

// §6.23 — even when wrapped in a larger expression, a member-access
// subtree inside type(...) is rejected.
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type operator argument shall not contain a hierarchical reference", 6,
      "6.23"));
}

// §6.23 — the inner expression of type(...) shall not reference an
// element of a dynamic object. A select whose base names a dynamic array
// is the smallest such reference.
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

// §6.23 — an associative array is also a dynamic object; selecting an
// element of one inside type(...) is rejected.
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

// §6.23 — a queue is a variable-size (dynamic) object as well, so selecting one
// of its elements inside type(...) is rejected, just like a dynamic or
// associative array element. This exercises the queue input form of the
// dynamic-object prohibition.
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

// §6.23 — a comparison of two type references is a constant expression, and the
// two references compare equal exactly when the referenced types match
// (§6.22.1) This is the accepting path for the `==` form: with `T` bound to
// `int`, the generate-if condition is true, so the then-block's declaration
// reaches the module and the else-block's does not. Observing which declaration
// survives shows the elaborator actually folding the comparison to true via
// type matching, not merely accepting the syntax.
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

// §6.23 — the rejecting path for `==`: `int` and `real` are nonmatching types,
// so the condition folds to false and the else-block is the one instantiated.
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

// §6.23 — the inequality form negates the match result: nonmatching types make
// `!=` true, selecting the then-block.
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

// §6.23 — the case-equality operator behaves the same as equality for type
// references: matching types fold `===` to true, selecting the then-block.
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

// §6.23 — the case-inequality operator negates the match, so matching types
// fold `!==` to false and the else-block is instantiated.
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

// §6.23 — both operands may be built-in data-type references rather than type
// parameters. `int` (signed) and `bit` (unsigned) are nonmatching, so the
// condition folds to false; the else-block is taken. This exercises the
// data-type (text) operand form of the fold, distinct from the type-parameter
// (identifier) form above.
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

// §6.23 — the comparison being a constant expression must hold for each kind of
// constant type operand, which take different resolution paths. The parameter
// form is covered above; here the operand is a `localparam type`, and the
// generate-if still folds by type matching (localparam T bound to `int` matches
// `type(int)`), selecting the then-block.
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

// A class declaring two typedefs of the same width and opposite signedness, so
// that a lookup reaching the wrong member is visible in the signedness rather
// than passing on a coincidence of width. `payload_t` is 8-bit signed and
// `beat_t` is 8-bit unsigned. The class stands ahead of the module because
// `Parser::ParseTypeRefExpr` resolves `Frame::payload_t` as a data type only
// once `Frame` is in the parser's known types.
constexpr const char* kFrameClass =
    "class Frame;\n"
    "  typedef byte payload_t;\n"
    "  typedef logic [7:0] beat_t;\n"
    "endclass\n";

// §8.23 — the type operator is one of the contexts in which a class scope
// resolution may prefix a type name, so `type(Frame::payload_t)` names the
// typedef declared in `Frame`. The width and signedness are the assertion: the
// declaration elaborates to a 1-bit unsigned logic when the prefix is not
// resolved, which the absence of a diagnostic alone would not show.
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

// §8.23 — the same for a net declaration, which reaches the check by a separate
// path through `Elaborator::ElaborateNetDecl`. The typedef is `beat_t` and not
// `payload_t` because §6.7.1 requires a net's data type to be 4-state, and
// `byte` is 2-state.
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

// §6.23 — exempting `::` does not exempt `.`: a member access into a module
// instance is still a hierarchical reference and is still rejected. The
// diagnostic and its subclause are what is asserted, so the test cannot pass on
// a rejection some other rule produced.
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
  const Diagnostic* diag = FindDiag(
      f, "type operator argument shall not contain a hierarchical reference");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "6.23");
}

// §6.23 — the exemption §8.23 grants applies to the scope resolution node
// itself and not to the subtree under it. `C::x.y` is a `.` member access whose
// left side is a `::` scope resolution, so the outer node is a hierarchical
// reference and the declaration is rejected.
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
  const Diagnostic* diag = FindDiag(
      f, "type operator argument shall not contain a hierarchical reference");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "6.23");
}

// §8.23 — the type-parameter-default form of the operator carries the class
// scope prefix as well, so `P` binds to `Frame::payload_t` and a variable
// declared with `P` is 8-bit signed. Losing the prefix binds `P` to a
// `payload_t` that no scope declares, which nothing diagnoses.
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

}  // namespace

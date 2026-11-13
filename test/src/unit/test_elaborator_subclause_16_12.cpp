#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <iterator>
#include <string>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/property_rewrite.h"
#include "elaborator/sampled_value.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

TEST(PropertyDeclarationElaboration, ExplicitDisableIffNestingRejected) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m(input logic clk, r1, r2, a, b);\n"
      "  property bad;\n"
      "    @(posedge clk) disable iff (r1) disable iff (r2) a |-> b;\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "this declaration's body is not one the grammar "
                            "admits",
                            3, "A.2.10"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "property \"bad\" nests disable iff clauses", 2,
                            "16.12"));
}

TEST(PropertyDeclarationElaboration,
     DisableIffNestingViaInstantiationRejected) {
  ElabFixture f;
  Elaborate(
      "module m(input logic clk, r1, a, b, r2);\n"
      "  property leaf;\n"
      "    @(posedge clk) disable iff (r1) a |-> b;\n"
      "  endproperty\n"
      "  property root;\n"
      "    @(posedge clk) disable iff (r2) leaf();\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "property \"root\" nests disable iff clauses", 5,
                            "16.12"));
}

TEST(PropertyDeclarationElaboration, SingleDisableIffNotFlaggedAsNested) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(input logic clk, rst, a, b);\n"
      "  property ok;\n"
      "    @(posedge clk) disable iff (rst) a |-> b;\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PropertyDeclarationElaboration,
     DisableIffNestingViaChainedInstantiationRejected) {
  ElabFixture f;
  Elaborate(
      "module m(input logic clk, r1, a, b, r2);\n"
      "  property leaf;\n"
      "    @(posedge clk) disable iff (r1) a |-> b;\n"
      "  endproperty\n"
      "  property mid;\n"
      "    @(posedge clk) leaf();\n"
      "  endproperty\n"
      "  property root;\n"
      "    @(posedge clk) disable iff (r2) mid();\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "property \"root\" nests disable iff clauses", 8,
                            "16.12"));
}

TEST(PropertyDeclarationElaboration,
     TwoSiblingDisableIffLeavesUnderOneRootRejected) {
  ElabFixture f;
  Elaborate(
      "module m(input logic clk, r1, a, b, r2, c, d);\n"
      "  property l1;\n"
      "    @(posedge clk) disable iff (r1) a |-> b;\n"
      "  endproperty\n"
      "  property l2;\n"
      "    @(posedge clk) disable iff (r2) c |-> d;\n"
      "  endproperty\n"
      "  property root;\n"
      "    @(posedge clk) l1() and l2();\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "property \"root\" nests disable iff clauses", 8,
                            "16.12"));
}

TEST(PropertyDeclarationElaboration,
     IndependentSingleDisableIffPropertiesAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(input logic clk, r1, a, b, r2, c, d);\n"
      "  property p1;\n"
      "    @(posedge clk) disable iff (r1) a |-> b;\n"
      "  endproperty\n"
      "  property p2;\n"
      "    @(posedge clk) disable iff (r2) c |-> d;\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PropertyDeclarationElaboration, SingleDisableIffViaInstantiationAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(input logic clk, r1, a, b);\n"
      "  property leaf;\n"
      "    @(posedge clk) disable iff (r1) a |-> b;\n"
      "  endproperty\n"
      "  property root;\n"
      "    @(posedge clk) leaf();\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(PropertyDeclarationElaboration, DisableConditionSampledValueNeedsClock) {
  EXPECT_TRUE(DisableConditionSampledValueClockIsWellFormed(
      SampledValueFunction::kSampled, false));
  EXPECT_TRUE(DisableConditionSampledValueClockIsWellFormed(
      SampledValueFunction::kSampled, true));
  EXPECT_FALSE(DisableConditionSampledValueRequiresExplicitClock(
      SampledValueFunction::kSampled));

  for (SampledValueFunction fn :
       {SampledValueFunction::kRose, SampledValueFunction::kFell,
        SampledValueFunction::kStable, SampledValueFunction::kChanged,
        SampledValueFunction::kPast}) {
    EXPECT_TRUE(DisableConditionSampledValueRequiresExplicitClock(fn));
    EXPECT_FALSE(DisableConditionSampledValueClockIsWellFormed(fn, false));
    EXPECT_TRUE(DisableConditionSampledValueClockIsWellFormed(fn, true));
  }
}

TEST(PropertyDeclarationElaboration, FlattenRejectsArgCountMismatch) {
  PropertyRegistry reg;
  ModuleItem decl;
  decl.kind = ModuleItemKind::kPropertyDecl;
  decl.name = "p";
  decl.prop_formals = {"a", "b"};
  reg.Register(&decl);

  auto fp = reg.Flatten("p", 1);
  EXPECT_FALSE(fp.legal);
}

TEST(PropertyDeclarationElaboration, FlattenAcceptsWellFormedProperty) {
  PropertyRegistry reg;
  ModuleItem decl;
  decl.kind = ModuleItemKind::kPropertyDecl;
  decl.name = "p";
  decl.prop_formals = {"x"};
  decl.prop_disable_iff_count = 1;
  reg.Register(&decl);

  auto fp = reg.Flatten("p", 1);
  EXPECT_TRUE(fp.legal);
  EXPECT_EQ(fp.disable_iff_count, 1);
  EXPECT_TRUE(PropertyRegistry::IsAcceptableAsTopLevelConcurrent(fp));
}

TEST(PropertyDependencyGraph, DefaultsAndActualsAreEdges) {
  Expr q2_ref;
  q2_ref.kind = ExprKind::kIdentifier;
  q2_ref.text = "q2";
  ModuleItem q1;
  q1.kind = ModuleItemKind::kPropertyDecl;
  q1.name = "q1";
  q1.prop_formals = {"x"};
  q1.prop_formal_defaults = {&q2_ref};
  ModuleItem q2;
  q2.kind = ModuleItemKind::kPropertyDecl;
  q2.name = "q2";
  q2.prop_instance_refs = {"q1"};
  Expr r1_ref;
  r1_ref.kind = ExprKind::kIdentifier;
  r1_ref.text = "r1";
  Expr r2_call;
  r2_call.kind = ExprKind::kCall;
  r2_call.callee = "r2";
  r2_call.args = {&r1_ref};
  PropertyExprNode r1_body;
  r1_body.boolean = &r2_call;
  ModuleItem r1;
  r1.kind = ModuleItemKind::kPropertyDecl;
  r1.name = "r1";
  r1.prop_instance_refs = {"r2"};
  r1.prop_body_tree = &r1_body;
  ModuleItem r2;
  r2.kind = ModuleItemKind::kPropertyDecl;
  r2.name = "r2";
  PropertyRegistry reg;
  for (const ModuleItem* item : {&q1, &q2, &r1, &r2}) reg.Register(item);
  EXPECT_TRUE(reg.IsRecursiveProperty(&q1));
  EXPECT_TRUE(reg.IsRecursiveProperty(&q2));
  EXPECT_TRUE(reg.IsRecursiveProperty(&r1));
  EXPECT_TRUE(reg.IsRecursiveProperty(&r2));
}

TEST(PropertyDollarActual, AnOperandFormalIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a, b;\n"
      "  property p1(m);\n"
      "    b == m;\n"
      "  endproperty\n"
      "  a1: assert property (@(posedge clk) a |-> p1($));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$ binds the formal 'm' of 'p1', which shall be "
                            "untyped",
                            6, "16.12"));
}

TEST(PropertyFlattening, AnInstanceWhoseFlattenedPropertyIsLegalIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  property p(x); @(posedge clk) x |-> b; endproperty\n"
      "  property q(x); @(posedge clk) a |-> x; endproperty\n"
      "  assert property (p(a ##1 b));\n"
      "  assert property (q(s_eventually b));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PropertyFlattening, DISABLED_AnInstanceWhoseFlattenedPropertyIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  property p(x); @(posedge clk) x |-> b; endproperty\n"
      "  assert property (p(s_eventually a));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "the flattened property of this instance of \"p\" is not legal", 4,
      "16.12"));
}

struct DollarForm {
  const char* support;
  const char* declaration;
  const char* arguments;
};

struct DollarSource {
  std::string src;
  uint32_t line;
};

constexpr const char* kDollarCheckedPlaces[] = {
    "module",    "assume",  "cover",  "procedural",
    "interface", "program", "checker"};

constexpr const char* kDollarUnprefixedPlaces[] = {
    "property", "import", "unit", "generate", "generate assertion"};

constexpr const char* kDollarPrefixedPlaces[] = {"package", "clocking",
                                                 "generate declaration"};

constexpr const char* kDollarUncheckedPlaces[] = {"import",
                                                  "unit",
                                                  "generate",
                                                  "generate assertion",
                                                  "package",
                                                  "clocking",
                                                  "generate declaration"};

std::vector<std::string> EachDollarPlace() {
  std::vector<std::string> places(std::begin(kDollarCheckedPlaces),
                                  std::end(kDollarCheckedPlaces));
  places.insert(places.end(), std::begin(kDollarUnprefixedPlaces),
                std::end(kDollarUnprefixedPlaces));
  places.insert(places.end(), std::begin(kDollarPrefixedPlaces),
                std::end(kDollarPrefixedPlaces));
  return places;
}

std::string DollarAssertion(const std::string& directive,
                            const std::string& instance) {
  return "  k: " + directive + " property (@(posedge clk) " + instance + ");\n";
}

std::string DollarInModule(const std::string& items) {
  return "module m;\n  bit clk, a, b;\n" + items + "endmodule\n";
}

std::string DollarInstancePrefix(const std::string& place) {
  if (place == "package") return "pk::";
  if (place == "clocking") return "cb.";
  if (place == "generate declaration") return "g.";
  return "";
}

std::string DollarInGenerate(const std::string& place,
                             const std::string& declarations,
                             const std::string& assertion) {
  if (place == "generate assertion") {
    return DollarInModule(declarations + "  if (1) begin : g\n" + assertion +
                          "  end\n");
  }
  if (place == "generate declaration") {
    return DollarInModule("  if (1) begin : g\n" + declarations + "  end\n" +
                          assertion);
  }
  return DollarInModule("  if (1) begin : g\n" + declarations + assertion +
                        "  end\n");
}

std::string DollarInDesignUnit(const std::string& place,
                               const std::string& declarations,
                               const std::string& assertion) {
  const std::string kInstance = DollarInModule("  w u(clk, a, b);\n");
  if (place == "checker") {
    return "checker w(clk, a, b);\n" + declarations + assertion +
           "endchecker\n" + kInstance;
  }
  return place + " w(input logic clk, a, b);\n" + declarations + assertion +
         "end" + place + "\n" + kInstance;
}

std::string DollarSourceIn(const std::string& place, const DollarForm& form,
                           const std::string& instance) {
  const std::string kDeclarations =
      std::string(form.support) + "  " + form.declaration + "\n";
  const std::string kAssertion = DollarAssertion("assert", instance);
  if (place == "assume" || place == "cover") {
    return DollarInModule(kDeclarations + DollarAssertion(place, instance));
  }
  if (place == "procedural") {
    return DollarInModule(kDeclarations +
                          "  always @(posedge clk) assert property "
                          "(@(posedge clk) " +
                          instance + ");\n");
  }
  if (place == "property") {
    return DollarInModule(kDeclarations + "  property outer; @(posedge clk) " +
                          instance +
                          "; endproperty\n  k: assert property (outer);\n");
  }
  if (place == "interface" || place == "program" || place == "checker") {
    return DollarInDesignUnit(place, kDeclarations, kAssertion);
  }
  if (place == "package" || place == "import") {
    return "package pk;\n" + kDeclarations + "endpackage\n" +
           DollarInModule((place == "import" ? "  import pk::*;\n" : "") +
                          kAssertion);
  }
  if (place == "unit") return kDeclarations + DollarInModule(kAssertion);
  if (place == "clocking") {
    return DollarInModule(std::string(form.support) +
                          "  clocking cb @(posedge clk);\n    " +
                          form.declaration + "\n  endclocking\n" + kAssertion);
  }
  if (place.starts_with("generate")) {
    return DollarInGenerate(place, kDeclarations, kAssertion);
  }
  return DollarInModule(kDeclarations + kAssertion);
}

DollarSource DollarIn(const std::string& place, const DollarForm& form) {
  const std::string kInstance =
      DollarInstancePrefix(place) + "p" + form.arguments;
  std::string src = DollarSourceIn(place, form, kInstance);
  const uint32_t kLine = LineHolding(src, "@(posedge clk) " + kInstance);
  return {std::move(src), kLine};
}

::testing::AssertionResult NoErrorReported(
    const std::vector<Diagnostic>& diags) {
  ::testing::AssertionResult result = ::testing::AssertionSuccess();
  bool clean = true;
  for (const auto& diag : diags) {
    if (diag.severity != DiagSeverity::kError) continue;
    if (clean) result = ::testing::AssertionFailure();
    clean = false;
    result << "\n  error at line " << diag.loc.line << " under §"
           << diag.subclause << ": " << diag.message;
  }
  return result;
}

size_t DollarReports(const std::vector<Diagnostic>& diags) {
  size_t count = 0;
  for (const auto& diag : diags) {
    if (diag.severity == DiagSeverity::kError &&
        diag.message.find("$ binds the formal") != std::string::npos) {
      ++count;
    }
  }
  return count;
}

void ExpectDollarAcceptedIn(const std::string& place, const DollarForm& form) {
  SCOPED_TRACE(form.arguments);
  SCOPED_TRACE(form.declaration);
  SCOPED_TRACE(place);
  ElabFixture f;
  ElaborateSrc(DollarIn(place, form).src, f);
  EXPECT_TRUE(NoErrorReported(f.diag.Diagnostics()));
}

struct ReportedDollar {
  DollarForm form;
  const char* formal;
  const char* owner;
  const char* clause;
};

void ExpectDollarReportedIn(const std::string& place,
                            const ReportedDollar& reported) {
  SCOPED_TRACE(reported.form.arguments);
  SCOPED_TRACE(reported.form.declaration);
  SCOPED_TRACE(place);
  ElabFixture f;
  const DollarSource kPlaced = DollarIn(place, reported.form);
  ElaborateSrc(kPlaced.src, f);
  std::string message = "$ binds the formal '";
  message += reported.formal;
  message += "' of '";
  message += reported.owner;
  message += "', which shall be untyped";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, kPlaced.line,
                            reported.clause));
  EXPECT_EQ(DollarReports(f.diag.Diagnostics()), 1u);
}

constexpr DollarForm kPermittedDollarForms[] = {
    {"", "property p(x, y, m); x |-> ##[1:m] y; endproperty", "(a, b, $)"},
    {"", "property p(x, y, m); x |-> y[*1:m]; endproperty", "(a, b, $)"},
    {"", "property p(x, y, m); x |-> y[->1:m]; endproperty", "(a, b, $)"},
    {"", "property p(x, y, m); x |-> y[=1:m]; endproperty", "(a, b, $)"},
    {"  sequence s(y, n); ##[1:n] y; endsequence\n",
     "property p(x, y, m); x |-> s(y, m); endproperty", "(a, b, $)"},
    {"  property r(x, y, n); x |-> ##[1:n] y; endproperty\n",
     "property p(x, y, m); r(x, y, m); endproperty", "(a, b, $)"},
    {"", "property p(x, y, m); x |-> y; endproperty", "(a, b, $)"},
    {"", "property p(x, y, untyped m); x |-> ##[1:m] y; endproperty",
     "(a, b, $)"},
    {"", "property p(x, y, untyped m); x |-> y; endproperty", "(a, b, $)"},
    {"", "property p(x, y, m = $); x |-> ##[1:m] y; endproperty", "(a, b)"},
};

constexpr DollarForm kRangeBoundDollarForms[] = {
    {"", "property p(x, y, m); always [1:m] y; endproperty", "(a, b, $)"},
    {"", "property p(x, y, m); s_eventually [1:m] y; endproperty", "(a, b, $)"},
};

constexpr DollarForm kOverriddenDollarDefault = {
    "", "property p(x, y, m = $); x |-> y == m; endproperty", "(a, b, 1)"};

constexpr DollarForm kNamedPermittedDollarForms[] = {
    {"", "property p(x, y, m); x |-> ##[1:m] y; endproperty",
     "(.m($), .y(b), .x(a))"},
    {"", "property p(x, y, m); x |-> ##[1:m] y; endproperty",
     "(a, .m($), .y(b))"},
};

constexpr ReportedDollar kNamedForbiddenDollarForms[] = {
    {{"", "property p(x, y, m); x |-> y == m; endproperty",
      "(.m($), .y(b), .x(a))"},
     "m",
     "p",
     "16.12"},
    {{"", "property p(x, y, m); x |-> ##[1:m] y; endproperty",
      "(.m(2), .x($), .y(b))"},
     "x",
     "p",
     "16.12"},
};

constexpr ReportedDollar kForbiddenDollarForms[] = {
    {{"", "property p(x, y, m); x |-> y == m; endproperty", "(a, b, $)"},
     "m",
     "p",
     "16.12"},
    {{"", "property p(x, y, m); x |-> ##[m:3] y; endproperty", "(a, b, $)"},
     "m",
     "p",
     "16.12"},
    {{"", "property p(x, y, m); x |-> y[*m:3]; endproperty", "(a, b, $)"},
     "m",
     "p",
     "16.12"},
    {{"", "property p(x, y, m); x |-> ##m y; endproperty", "(a, b, $)"},
     "m",
     "p",
     "16.12"},
    {{"", "property p(x, y, m); x |-> y[*m]; endproperty", "(a, b, $)"},
     "m",
     "p",
     "16.12"},
    {{"", "property p(x, y, m); eventually [1:m] y; endproperty", "(a, b, $)"},
     "m",
     "p",
     "16.12"},
    {{"", "property p(x, y, m); s_always [1:m] y; endproperty", "(a, b, $)"},
     "m",
     "p",
     "16.12"},
    {{"", "property p(x, y, m); nexttime [m] y; endproperty", "(a, b, $)"},
     "m",
     "p",
     "16.12"},
    {{"", "property p(x, y, m); s_nexttime [m] y; endproperty", "(a, b, $)"},
     "m",
     "p",
     "16.12"},
    {{"", "property p(x, y, m); x |-> $past(y, m); endproperty", "(a, b, $)"},
     "m",
     "p",
     "16.12"},
    {{"", "property p(x, y, int m); x |-> ##[1:m] y; endproperty", "(a, b, $)"},
     "m",
     "p",
     "16.12"},
    {{"", "property p(x, y, bit [3:0] m); x |-> ##[1:m] y; endproperty",
      "(a, b, $)"},
     "m",
     "p",
     "16.12"},
    {{"", "property p(x, y, sequence m); x |-> y; endproperty", "(a, b, $)"},
     "m",
     "p",
     "16.12"},
    {{"", "property p(x, y, property m); x |-> y; endproperty", "(a, b, $)"},
     "m",
     "p",
     "16.12"},
    {{"", "property p(x, y, event m); x |-> y; endproperty", "(a, b, $)"},
     "m",
     "p",
     "16.12"},
};

constexpr ReportedDollar kFunctionArgumentDollarForm = {
    {"  function automatic bit f(bit v); return v; endfunction\n",
     "property p(x, y, m); x |-> y == f(m); endproperty", "(a, b, $)"},
    "m",
    "p",
    "16.12"};

constexpr ReportedDollar kPassedOnDollarForms[] = {
    {{"  sequence sop(y, n); y ##1 (y == n); endsequence\n",
      "property p(x, y, m); x |-> sop(y, m); endproperty", "(a, b, $)"},
     "n",
     "sop",
     "16.8"},
    {{"  sequence si(y, int n); ##[1:n] y; endsequence\n",
      "property p(x, y, m); x |-> si(y, m); endproperty", "(a, b, $)"},
     "n",
     "si",
     "16.8"},
    {{"  property pop(x, y, n); x |-> y == n; endproperty\n",
      "property p(x, y, m); pop(x, y, m); endproperty", "(a, b, $)"},
     "n",
     "pop",
     "16.12"},
};

constexpr ReportedDollar kDefaultDollarForms[] = {
    {{"", "property p(x, y, m = $); x |-> y == m; endproperty", "(a, b)"},
     "m",
     "p",
     "16.12"},
    {{"", "property p(x, y, int m = $); x |-> ##[1:m] y; endproperty",
      "(a, b)"},
     "m",
     "p",
     "16.12"},
};

TEST(PropertyDollarActual, APermittedReferenceIsAcceptedInEachUnprefixedPlace) {
  for (const DollarForm& form : kPermittedDollarForms) {
    for (const char* place : kDollarCheckedPlaces) {
      ExpectDollarAcceptedIn(place, form);
    }
    for (const char* place : kDollarUnprefixedPlaces) {
      ExpectDollarAcceptedIn(place, form);
    }
  }
}

TEST(PropertyDollarActual,
     DISABLED_APermittedReferenceIsAcceptedThroughAPackageClockingOrGenerate) {
  for (const DollarForm& form : kPermittedDollarForms) {
    for (const char* place : kDollarPrefixedPlaces) {
      ExpectDollarAcceptedIn(place, form);
    }
  }
}

TEST(PropertyDollarActual,
     DISABLED_AnAlwaysOrSEventuallyRangeMaximumIsAcceptedInEachPlace) {
  for (const DollarForm& form : kRangeBoundDollarForms) {
    for (const std::string& place : EachDollarPlace()) {
      ExpectDollarAcceptedIn(place, form);
    }
  }
}

TEST(PropertyDollarActual,
     DISABLED_ADefaultTheInstanceOverridesIsAcceptedInEachPlace) {
  for (const std::string& place : EachDollarPlace()) {
    ExpectDollarAcceptedIn(place, kOverriddenDollarDefault);
  }
}

TEST(PropertyDollarActual,
     DISABLED_ADollarBoundByNameIsJudgedAgainstItsFormalInEachPlace) {
  for (const std::string& place : EachDollarPlace()) {
    for (const DollarForm& form : kNamedPermittedDollarForms) {
      ExpectDollarAcceptedIn(place, form);
    }
    for (const ReportedDollar& reported : kNamedForbiddenDollarForms) {
      ExpectDollarReportedIn(place, reported);
    }
  }
}

TEST(PropertyDollarActual, AForbiddenReferenceIsReportedOnceInACheckedPlace) {
  for (const ReportedDollar& reported : kForbiddenDollarForms) {
    for (const char* place : kDollarCheckedPlaces) {
      ExpectDollarReportedIn(place, reported);
    }
  }
}

TEST(PropertyDollarActual,
     DISABLED_AForbiddenReferenceIsReportedOnceInsideAnotherProperty) {
  for (const ReportedDollar& reported : kForbiddenDollarForms) {
    ExpectDollarReportedIn("property", reported);
  }
}

TEST(PropertyDollarActual,
     DISABLED_AForbiddenReferenceIsReportedInEachUncheckedPlace) {
  for (const ReportedDollar& reported : kForbiddenDollarForms) {
    for (const char* place : kDollarUncheckedPlaces) {
      ExpectDollarReportedIn(place, reported);
    }
  }
}

TEST(PropertyDollarActual,
     DISABLED_AFunctionCallArgumentIsReportedInEachPlace) {
  for (const std::string& place : EachDollarPlace()) {
    ExpectDollarReportedIn(place, kFunctionArgumentDollarForm);
  }
}

TEST(PropertyDollarActual,
     DISABLED_ADollarPassedOnToAnOperandOrTypedFormalIsReportedInEachPlace) {
  for (const ReportedDollar& reported : kPassedOnDollarForms) {
    for (const std::string& place : EachDollarPlace()) {
      ExpectDollarReportedIn(place, reported);
    }
  }
}

TEST(PropertyDollarActual,
     DISABLED_ADollarDefaultOfAnOperandOrTypedFormalIsReportedOnceInEachPlace) {
  for (const ReportedDollar& reported : kDefaultDollarForms) {
    for (const std::string& place : EachDollarPlace()) {
      ExpectDollarReportedIn(place, reported);
    }
  }
}

}  // namespace

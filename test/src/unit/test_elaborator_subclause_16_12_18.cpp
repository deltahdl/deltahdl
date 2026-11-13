#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "elaborator/rtlir.h"
#include "elaborator/typed_property_formal.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

const RtlirProcess* TheAssertionProcess(const RtlirModule* mod) {
  for (const auto& p : mod->processes) {
    if (p.kind == RtlirProcessKind::kAlwaysFF) return &p;
  }
  return nullptr;
}

TEST(TypedPropertyFormal, AnEventActualSuppliesTheInstancesClock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  property p_ev(event ev);\n"
      "    @(ev) a |-> b;\n"
      "  endproperty\n"
      "  assert property (p_ev(negedge clk));\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirProcess* p = TheAssertionProcess(design->top_modules[0]);
  ASSERT_NE(p, nullptr);
  ASSERT_EQ(p->sensitivity.size(), 1u);
  EXPECT_EQ(p->sensitivity[0].edge, Edge::kNegedge);
  ASSERT_NE(p->sensitivity[0].signal, nullptr);
  EXPECT_EQ(p->sensitivity[0].signal->text, "clk");
}

TEST(TypedPropertyFormal, SequenceRulesCarryOverExceptOverriddenAspects) {
  EXPECT_TRUE(PropertyFormalInheritsSequenceRule(
      PropertyFormalRuleAspect::kActualArgumentSubstitution));
  EXPECT_FALSE(PropertyFormalInheritsSequenceRule(
      PropertyFormalRuleAspect::kAllowedTypeList));
  EXPECT_FALSE(PropertyFormalInheritsSequenceRule(
      PropertyFormalRuleAspect::kTypedReferencePlacement));
}

TEST(TypedPropertyFormal,
     AllowedTypeKindsIncludePropertySequenceEventOrDataType) {
  EXPECT_TRUE(IsPropertyFormalTypeAllowed(PropertyFormalTypeKind::kProperty));
  EXPECT_TRUE(IsPropertyFormalTypeAllowed(PropertyFormalTypeKind::kSequence));
  EXPECT_TRUE(IsPropertyFormalTypeAllowed(PropertyFormalTypeKind::kEvent));
  EXPECT_TRUE(IsPropertyFormalTypeAllowed(
      PropertyFormalTypeKind::kAssertionExpressionType));
}

TEST(TypedPropertyFormal, ForbiddenTypeKindRejected) {
  EXPECT_FALSE(IsPropertyFormalTypeAllowed(PropertyFormalTypeKind::kForbidden));
}

TEST(TypedPropertyFormal, PropertyTypedActualMustBePropertyExpr) {
  EXPECT_TRUE(IsPropertyTypedFormalActualLegal(
      PropertyTypedFormalActualKind::kPropertyExpr));
  EXPECT_TRUE(IsPropertyTypedFormalActualLegal(
      PropertyTypedFormalActualKind::kBooleanExpression));
  EXPECT_TRUE(IsPropertyTypedFormalActualLegal(
      PropertyTypedFormalActualKind::kSequenceExpr));
  EXPECT_FALSE(IsPropertyTypedFormalActualLegal(
      PropertyTypedFormalActualKind::kNotAPropertyExpr));
}

TEST(TypedPropertyFormal, PropertyTypedRefLegalOnlyWherePropertyExprAllowed) {
  EXPECT_TRUE(IsPropertyTypedFormalRefLegal(
      PropertyTypedFormalRefPlace::kPropertyExprPosition));
  EXPECT_FALSE(IsPropertyTypedFormalRefLegal(
      PropertyTypedFormalRefPlace::kImplicationAntecedent));
  EXPECT_FALSE(IsPropertyTypedFormalRefLegal(
      PropertyTypedFormalRefPlace::kOtherPosition));
}

TEST(TypedPropertyFormal, ATreeActualGivesABooleanBodysInstanceATree) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, b, c;\n"
      "  property p_not(property q);\n"
      "    @(posedge clk) not q;\n"
      "  endproperty\n"
      "  assert property (p_not(b |-> c));\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirProcess* p = TheAssertionProcess(design->top_modules[0]);
  ASSERT_NE(p, nullptr);
  ASSERT_NE(p->body, nullptr);
  EXPECT_FALSE(p->body->assert_negated);
  const PropertyExprNode* root = p->body->assert_property;
  ASSERT_NE(root, nullptr);
  EXPECT_EQ(root->kind, PropertyExprNode::Kind::kBoolean);
  ASSERT_NE(root->boolean, nullptr);
  EXPECT_EQ(root->boolean->kind, ExprKind::kCall);
  ASSERT_EQ(root->boolean->args.size(), 1u);
  const PropertyExprNode* actual = root->boolean->args[0]->property_actual;
  ASSERT_NE(actual, nullptr);
  EXPECT_EQ(actual->kind, PropertyExprNode::Kind::kImplication);
}

struct PlacedActual {
  std::string src;
  uint32_t line;
};

PlacedActual ActualIn(const std::string& place, const std::string& inst) {
  const std::string kDecls =
      "property p(property q); q; endproperty property p2(event e, property "
      "q); @(e) q; endproperty";
  const std::string kSignals = "bit clk, a, b, rst; ";
  std::string spec = "@(posedge clk) " + inst;
  if (place == "package") {
    return {"package pk;\n  " + kDecls +
                "\nendpackage\nmodule m;\n  import pk::*; " + kSignals +
                "\n  k: assert property (" + spec + ");\nendmodule\n",
            6};
  }
  if (place == "unit") {
    return {"\n  " + kDecls + "\nmodule m;\n  " + kSignals +
                "\n  k: assert property (" + spec + ");\nendmodule\n",
            5};
  }
  std::string line = "  k: assert property (" + spec + ");";
  if (place == "assume" || place == "cover") {
    line = "  k: " + place + " property (" + spec + ");";
  }
  if (place == "procedural") {
    line = "  always @(posedge clk) assert property (" + inst + ");";
  }
  if (place == "property") {
    line = "  property r; @(posedge clk) a |-> " + inst + "; endproperty";
  }
  if (place == "generate") line = "  if (1) begin : g" + line + " end";
  std::string body = "  " + kSignals + kDecls + "\n" + line + "\n";
  if (place == "interface" || place == "program" || place == "checker") {
    return {place + " m;\n" + body + "end" + place +
                "\nmodule top; m u(); endmodule\n",
            3};
  }
  return {"module m;\n" + body + "endmodule\n", 3};
}

constexpr const char* kActualPlaces[] = {
    "module",    "assume",  "cover",   "procedural", "property", "generate",
    "interface", "program", "checker", "package",    "unit"};

TEST(TypedPropertyFormal,
     DISABLED_AnEventActualOfAPropertyFormalIsReportedInEachPlace) {
  for (const char* place : kActualPlaces) {
    for (const char* inst :
         {"p(posedge clk)", "p(negedge clk)", "p(edge clk)",
          "p(posedge clk or negedge rst)", "p(posedge clk iff a)",
          "p(.q(posedge clk))", "p2(posedge clk, posedge clk)"}) {
      SCOPED_TRACE(std::string(place) + " " + inst);
      ElabFixture f;
      PlacedActual placed = ActualIn(place, inst);
      ElaborateSrc(placed.src, f);
      EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                                "the actual of the 'property'-typed formal 'q'",
                                placed.line, "16.12.18"));
    }
  }
}

TEST(TypedPropertyFormal, APropertyExprActualIsAcceptedInEachPlace) {
  for (const char* place : kActualPlaces) {
    for (const char* inst :
         {"p(clk)", "p(!clk)", "p(clk or !rst)", "p(clk && a)", "p(1)",
          "p(a ##1 b)", "p(a or nexttime b)", "p(@(posedge clk) a)",
          "p(.q(a ##1 b))", "p2(posedge clk, a)"}) {
      SCOPED_TRACE(std::string(place) + " " + inst);
      ElabFixture f;
      ElaborateSrc(ActualIn(place, inst).src, f);
      EXPECT_FALSE(f.has_errors);
    }
  }
}

void ExpectDollarActualReported(const char* place) {
  SCOPED_TRACE(place);
  ElabFixture f;
  PlacedActual placed = ActualIn(place, "p($)");
  ElaborateSrc(placed.src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$ binds the formal 'q' of 'p', which shall be "
                            "untyped",
                            placed.line, "16.12"));
}

TEST(TypedPropertyFormal, ADollarActualOfAPropertyFormalIsReportedInEachPlace) {
  for (const char* place : {"module", "assume", "cover", "procedural",
                            "property", "interface", "program", "checker"}) {
    ExpectDollarActualReported(place);
  }
}

TEST(
    TypedPropertyFormal,
    DISABLED_ADollarActualOfAPropertyFormalIsReportedInAGeneratePackageOrUnit) {
  for (const char* place : {"generate", "package", "unit"}) {
    ExpectDollarActualReported(place);
  }
}

TEST(TypedPropertyFormal, DISABLED_AnEventDefaultOfAPropertyFormalIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a, b; property pd(property q = posedge clk); q; "
      "endproperty\n"
      "  k: assert property (@(posedge clk) pd);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the actual of the 'property'-typed formal 'q'", 3,
                            "16.12.18"));
}

TEST(TypedPropertyFormal, APropertyExprDefaultOfAPropertyFormalIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a, b; property pd(property q = a ##1 b); q; endproperty\n"
      "  k: assert property (@(posedge clk) pd);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

constexpr const char* kFormalTypeDefinitions =
    "interface ifc; endinterface\n"
    "package tp; typedef union {int i; byte c;} u_t; typedef real ra_t[2]; "
    "typedef struct {real r;} rs_t; typedef event ea_t[2]; class lc; local "
    "int k; endclass typedef enum {E0, E1} e_t; typedef struct packed {bit "
    "[3:0] f;} ps_t; typedef int ia_t[2]; class pc; int k; endclass "
    "endpackage\n";

std::string FormalTypeIn(const std::string& place, const std::string& type) {
  const std::string kDeclared = "property p(" + type + " x); 1; endproperty";
  if (place == "unit") {
    return std::string(kFormalTypeDefinitions) + "import tp::*;\n  " +
           kDeclared + "\n";
  }
  std::string line = "  " + kDeclared;
  if (place == "generate") line = "  if (1) begin : g " + kDeclared + " end";
  if (place == "clocking") {
    line = "  clocking cb @(posedge clk); " + kDeclared + " endclocking";
  }
  std::string unit =
      place == "generate" || place == "clocking" ? "module" : place;
  return std::string(kFormalTypeDefinitions) + unit +
         " m; import tp::*; bit clk;\n" + line + "\nend" + unit + "\n";
}

constexpr const char* kFormalTypePlaces[] = {
    "module",  "interface", "program",  "checker",
    "package", "generate",  "clocking", "unit"};

TEST(TypedPropertyFormal, AnAllowedFormalTypeIsAcceptedInEachPlace) {
  for (const char* place : kFormalTypePlaces) {
    for (const char* type :
         {"", "property", "sequence", "event", "bit", "logic [3:0]", "int",
          "byte", "real", "shortreal", "realtime", "string", "e_t", "ps_t",
          "ia_t", "pc"}) {
      SCOPED_TRACE(std::string(place) + " " + type);
      ElabFixture f;
      ElaborateSrc(FormalTypeIn(place, type), f);
      EXPECT_FALSE(f.has_errors);
    }
  }
}

TEST(TypedPropertyFormal, AChandleFormalIsReportedInEachPlace) {
  for (const char* place : kFormalTypePlaces) {
    SCOPED_TRACE(place);
    ElabFixture f;
    ElaborateSrcAllowingParseErrors(FormalTypeIn(place, "chandle"), f);
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "a sequence or property formal argument may not be of type chandle", 4,
        "16.8"));
  }
}

TEST(TypedPropertyFormal,
     DISABLED_AFormalTypeNoAssertionExpressionMayHaveIsReportedInEachPlace) {
  for (const char* place : kFormalTypePlaces) {
    for (const char* type :
         {"u_t", "ra_t", "rs_t", "ea_t", "lc", "virtual ifc"}) {
      SCOPED_TRACE(std::string(place) + " " + type);
      ElabFixture f;
      ElaborateSrc(FormalTypeIn(place, type), f);
      EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                                "the formal argument 'x' of 'p' is of a type "
                                "other than property, sequence, event or one "
                                "an assertion expression may have",
                                4, "16.12.18"));
    }
  }
}

}  // namespace

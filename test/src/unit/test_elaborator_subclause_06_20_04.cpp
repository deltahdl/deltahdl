#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(LocalparamElaboration, ParameterAndLocalparamCoexist) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter int WIDTH = 8;\n"
      "  localparam int DEPTH = 16;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found_width = false, found_depth = false;
  for (const auto& p : mod->params) {
    if (p.name == "WIDTH") {
      EXPECT_EQ(p.resolved_value, 8);
      EXPECT_FALSE(p.is_localparam);
      found_width = true;
    }
    if (p.name == "DEPTH") {
      EXPECT_EQ(p.resolved_value, 16);
      EXPECT_TRUE(p.is_localparam);
      found_depth = true;
    }
  }
  EXPECT_TRUE(found_width);
  EXPECT_TRUE(found_depth);
}

TEST(LocalparamElaboration, LocalparamDerivedFromParameter) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter int WIDTH = 8;\n"
      "  localparam int DOUBLE = WIDTH * 2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& p : mod->params) {
    if (p.name == "DOUBLE") {
      EXPECT_TRUE(p.is_resolved);
      EXPECT_EQ(p.resolved_value, 16);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(LocalparamElaboration, ImplicitTypeLocalparamResolvesValue) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  localparam X = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& p : mod->params) {
    if (p.name == "X") {
      found = true;
      EXPECT_TRUE(p.is_localparam);
      EXPECT_TRUE(p.is_resolved);
      EXPECT_EQ(p.resolved_value, 42);
    }
  }
  EXPECT_TRUE(found);
}

// §23.10.1 states the rule for the defparam statement, so the report names that
// subclause rather than §6.20.4.
TEST(LocalparamElaboration, DefparamOnLocalparamIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module child;\n"
      "  localparam int WIDTH = 4;\n"
      "endmodule\n"
      "module top;\n"
      "  child u0();\n"
      "  defparam u0.WIDTH = 16;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "defparam cannot override a local parameter", 6,
                            "23.10.1"));
}

// §6.20.4: a localparam cannot be modified by an instance parameter value
// assignment. A named override that targets a localparam port is rejected
// because the localparam is not an overridable parameter of the instance.
TEST(LocalparamElaboration, NamedInstanceOverrideOfLocalparamIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module child #(localparam int LP = 4)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.LP(9)) u0();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module 'child' has no parameter 'LP'", 4,
                            "23.10.2.2"));
}

// §6.20.4: the same prohibition applies to positional overrides, which only
// target nonlocal parameters; supplying one when the port list has only a
// localparam is an error.
TEST(LocalparamElaboration, PositionalInstanceOverrideOfLocalparamIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module child #(localparam int LP = 4)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(9) u0();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "too many positional parameter overrides for module 'child'", 4,
      "23.10.2.1"));
}

// §6.20.4: a localparam is assigned a constant expression containing a
// parameter, which in turn can be modified by an instance parameter value
// assignment; the localparam follows the overridden parameter value.
TEST(LocalparamElaboration, LocalparamFollowsOverriddenParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int W = 8);\n"
      "  localparam int W2 = W * 2;\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.W(16)) u0();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  ASSERT_FALSE(top->children.empty());
  auto* child = top->children[0].resolved;
  ASSERT_NE(child, nullptr);
  bool found = false;
  for (const auto& p : child->params) {
    if (p.name == "W2") {
      found = true;
      EXPECT_TRUE(p.is_localparam);
      EXPECT_TRUE(p.is_resolved);
      EXPECT_EQ(p.resolved_value, 32);
    }
  }
  EXPECT_TRUE(found);
}

// §6.20.4: the parameter a localparam is derived from may be modified by a
// defparam statement (not only by an instance parameter value assignment); the
// localparam follows the defparam'd value. Distinct from the instance-override
// path: W is changed by defparam and the dependent localparam W2 is recomputed.
TEST(LocalparamElaboration, LocalparamFollowsDefparamModifiedParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int W = 8);\n"
      "  localparam int W2 = W * 2;\n"
      "endmodule\n"
      "module top;\n"
      "  child u0();\n"
      "  defparam u0.W = 16;\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* child = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(child, nullptr);
  bool found = false;
  for (const auto& p : child->params) {
    if (p.name == "W2") {
      found = true;
      EXPECT_TRUE(p.is_localparam);
      EXPECT_TRUE(p.is_resolved);
      EXPECT_EQ(p.resolved_value, 32);
    }
  }
  EXPECT_TRUE(found);
}

// §6.20.4: in a parameter_port_list a declaration with no keyword inherits the
// preceding localparam group, so it is a local parameter and therefore not
// overridable. Here C follows a localparam B, so a named instance override of C
// is rejected — observing the sticky-grouping classification through the full
// elaboration path.
TEST(LocalparamElaboration, StickyLocalparamPortRejectsInstanceOverride) {
  ElabFixture f;
  ElaborateSrc(
      "module child #(parameter int A = 1, localparam int B = 2, int C = "
      "3)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.C(9)) u0();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module 'child' has no parameter 'C'", 4,
                            "23.10.2.2"));
}

// §6.20.4: a localparam "can be assigned constant expressions (see 11.2.1)",
// and §11.2.1 does not list a variable among the operands one consists of. The
// initializer here is a bare identifier naming a variable, which is the
// simplest spelling of the rule and the one that shows the check tests the
// expression rather than its ExprKind.
TEST(LocalparamElaboration, NonConstantIdentifierInitializerIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int v;\n"
      "  localparam int N = v;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "localparam 'N' initializer is not a constant expression", 3, "6.20.4"));
}

// §6.20.4: the operand rules of §11.2.1 reach through the operators of
// Table 11-1, so a variable is no more constant inside a binary expression than
// alone. This is the commonest spelling of a non-constant initializer, and a
// check written for bare identifiers alone would leave it unreported.
TEST(LocalparamElaboration, NonConstantBinaryInitializerIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int v;\n"
      "  localparam int N = v + 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "localparam 'N' initializer is not a constant expression", 3, "6.20.4"));
}

// §6.20.4 with §8.25: a class specialization's override is a constant
// expression, so `C#(v)::P` with `v` a variable names no parameter that has a
// value. ConstEvalMemberAccessFull refuses to fold such an override rather than
// returning the class's own default, and this is the report that refusal has to
// reach.
TEST(LocalparamElaboration, SpecializationOverrideThatDoesNotFoldIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C #(int P = 1);\n"
      "endclass\n"
      "module m;\n"
      "  int v;\n"
      "  localparam int N = C#(v)::P;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "localparam 'N' initializer is not a constant expression", 5, "6.20.4"));
}

// §6.20.4: a localparam is "assigned constant expressions ... containing
// parameters", so an initializer naming another parameter is exactly what the
// clause permits. This is what the check above must not reject.
TEST(LocalparamElaboration, ConstantIdentifierInitializerIsAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  localparam int K = 4;\n"
      "  localparam int N = K;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §6.20.4: "local parameters can be declared in a generate block, package,
// class body, or compilation-unit scope. In these contexts, the parameter
// keyword shall be a synonym for the localparam keyword." The nine cases below
// vary the scope the declaration sits in while holding the initializer fixed at
// the bare identifier NonConstantIdentifierInitializerIsReported uses, because
// the scope is what the check was keyed on: it read a module's top-level items
// alone, so every case above passes whether or not any other scope is reached.

// A conditional generate block. Its items are in ModuleItem::gen_body rather
// than in the module's item list, which is what the module-level loop reads.
TEST(LocalparamElaboration, NonConstantInitializerInAGenerateBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int v;\n"
      "  if (1) begin\n"
      "    localparam int N = v;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "localparam 'N' initializer is not a constant expression", 4, "6.20.4"));
}

// The else arm, which Parser::ParseGenerateIf hangs off ModuleItem::gen_else as
// a second generate item rather than storing beside the then arm. A walk that
// read gen_body alone would leave this declaration unvisited.
TEST(LocalparamElaboration,
     NonConstantInitializerInAGenerateElseArmIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int v;\n"
      "  if (0) begin\n"
      "    localparam int A = 1;\n"
      "  end else begin\n"
      "    localparam int B = v;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "localparam 'B' initializer is not a constant expression", 6, "6.20.4"));
}

// A case arm, whose items are in ModuleItem::gen_case_items[].body and in
// neither of the two vectors the cases above reach.
TEST(LocalparamElaboration,
     NonConstantInitializerInAGenerateCaseArmIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int v;\n"
      "  localparam int S = 0;\n"
      "  case (S)\n"
      "    0: begin\n"
      "      localparam int N = v;\n"
      "    end\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "localparam 'N' initializer is not a constant expression", 6, "6.20.4"));
}

// A package, which is not a module and is elaborated through no module's item
// pass at all.
TEST(LocalparamElaboration, NonConstantInitializerInAPackageIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  int v;\n"
      "  localparam int N = v;\n"
      "endpackage\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "localparam 'N' initializer is not a constant expression", 3, "6.20.4"));
}

// The synonym half of the clause, which no other case here reads: the
// declaration says `parameter`, and in a package that word means `localparam`,
// so the constant-expression rule applies to it. A check keyed on the
// `localparam` keyword alone passes every case above and misses this one.
TEST(LocalparamElaboration,
     NonConstantPackageParameterIsReportedAsALocalparam) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  int v;\n"
      "  parameter int N = v;\n"
      "endpackage\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "localparam 'N' initializer is not a constant expression", 3, "6.20.4"));
}

// Compilation-unit scope, where the declaration was previously dropped from the
// elaborator's constant scope without a word when its initializer did not fold.
TEST(LocalparamElaboration,
     NonConstantInitializerAtCompilationUnitScopeIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "int v;\n"
      "localparam int N = v;\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "localparam 'N' initializer is not a constant expression", 2, "6.20.4"));
}

// §6.20.1 lets a declaration read one made before it in the same block, and the
// scope a generate body is folded against is not the module's. Without this
// case a walk that judged every body declaration against the module's
// parameters alone would report N and pass all six cases above.
TEST(LocalparamElaboration, ConstantInitializerInAGenerateBlockIsAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  if (1) begin\n"
      "    localparam int K = 4;\n"
      "    localparam int N = K + 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §27.4 makes the loop index an implicit localparam of the block, so an
// initializer reading it is a constant expression. The index is in no scope the
// module holds, so a walk that did not bind it would reject this source.
TEST(LocalparamElaboration, GenvarInitializerInAGenerateLoopIsAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  genvar g;\n"
      "  for (g = 0; g < 2; g = g + 1) begin : b\n"
      "    localparam int L = g + 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The same §6.20.1 dependence inside a package. A package parameter is recorded
// in the compilation-unit scope under its "p.K" key alone (§26.3), so a check
// folding K's bare name against that scope would reject N here.
TEST(LocalparamElaboration, PackageLocalparamReadingAnEarlierOneIsAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "package p;\n"
      "  localparam int K = 4;\n"
      "  localparam int N = K + 1;\n"
      "endpackage\n"
      "module m;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace

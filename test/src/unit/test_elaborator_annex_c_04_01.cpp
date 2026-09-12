// Annex C.4.1: defparam statements. The statement is identified for
// deprecation, and "this current standard still requires tools to support"
// it, in the placements the subclause names as what makes it costly: before
// or after the instance it modifies, at the end of the file, in a separate
// file, and hierarchically. A defparam written in a separate file is one
// written in a module of its own, which names the instance it modifies from
// the root of the hierarchy: §23.8 resolves a name whose leading step names no
// scope of the writing module upward, and the root it reaches is a top-level
// module, which is how §23.10.4.2's own example, `defparam m.n.p = 1;` written
// in the m1 that m instantiates, reaches m's instance n. These cases observe
// the elaborator supporting each placement.

#include <cstdint>
#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

const RtlirModule* FirstChild(const RtlirModule* mod) {
  if (mod == nullptr || mod->children.empty()) return nullptr;
  return mod->children[0].resolved;
}

int64_t ParamValue(const RtlirModule* mod, std::string_view name) {
  if (mod == nullptr) return -1;
  for (const auto& p : mod->params) {
    if (p.name == name) return p.resolved_value;
  }
  return -1;
}

// C.4.1: "A defparam statement can precede the instance to be modified".
TEST(DefparamSupport, DefparamBeforeTheInstanceApplies) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module leaf #(parameter int P = 1)(); endmodule\n"
      "module top;\n"
      "  defparam u.P = 5;\n"
      "  leaf u();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(FirstChild(design->top_modules[0]), "P"), 5);
}

// C.4.1: "can be in a separate file from the instance to be modified". A
// separate file holds a module of its own, a top-level one, whose defparam
// names the instance from the top-level module that holds it.
TEST(DefparamSupport, DefparamInASeparateTopModuleReachesTheInstance) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module leaf #(parameter int P = 1)(); endmodule\n"
      "module top;\n"
      "  leaf u1();\n"
      "endmodule\n"
      "module annotate;\n"
      "  defparam top.u1.P = 7;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 2u);
  EXPECT_EQ(ParamValue(FirstChild(design->top_modules[0]), "P"), 7);
}

// The same from a separate top, naming the top-level module's own parameter:
// the root of the path is the module the parameter is declared in.
TEST(DefparamSupport, DefparamInASeparateTopModuleReachesTheTopsParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top #(parameter int P = 1)(); endmodule\n"
      "module annotate;\n"
      "  defparam top.P = 9;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 2u);
  EXPECT_EQ(ParamValue(design->top_modules[0], "P"), 9);
}

// §23.10.4.2's example, with the generate block renamed as its last paragraph
// says: the defparam in m1 names m1's own instance through the top-level
// module m, sets its p to 1, and the generate condition reading p selects the
// block, so m1 holds the m2 instance it wrote there.
TEST(DefparamSupport, DefparamThroughTheTopLevelModuleReachesTheWriter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  m1 n();\n"
      "endmodule\n"
      "module m1;\n"
      "  parameter p = 2;\n"
      "  defparam m.n.p = 1;\n"
      "  if (p == 1) begin : gen_unique\n"
      "    m2 n();\n"
      "  end\n"
      "endmodule\n"
      "module m2;\n"
      "  parameter p = 3;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirModule* m1 = FirstChild(design->top_modules[0]);
  EXPECT_EQ(ParamValue(m1, "p"), 1);
  EXPECT_NE(FirstChild(m1), nullptr);
}

// C.4.1: a defparam "can modify parameters hierarchically that are in turn
// passed to other defparam statements to modify", so a defparam whose target
// another defparam reads on its right-hand side is applied first, §23.10.4.1
// deferring a statement whose target is not yet resolved.
TEST(DefparamSupport, DefparamValueFlowsIntoAnotherDefparam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module leaf #(parameter int P = 1)(); endmodule\n"
      "module mid #(parameter int Q = 2);\n"
      "  leaf u();\n"
      "  defparam u.P = Q;\n"
      "endmodule\n"
      "module top;\n"
      "  mid v();\n"
      "  defparam v.Q = 8;\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirModule* mid = FirstChild(design->top_modules[0]);
  EXPECT_EQ(ParamValue(mid, "Q"), 8);
  EXPECT_EQ(ParamValue(FirstChild(mid), "P"), 8);
}

// A path through the top that names no parameter of it reaches nothing, and
// is the warning §23.10.1 gives an unresolved target.
TEST(DefparamSupport, DefparamNamingNoParameterOfTheTopWarns) {
  ElabFixture f;
  ElaborateSrc(
      "module top #(parameter int P = 1)(); endmodule\n"
      "module annotate;\n"
      "  defparam top.NOPE = 9;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(), "defparam target not found",
                              3, "23.10.1"));
}

// §23.10.1 holds for a path through the top as for one through the writer's
// own instances: a defparam in a generate block "shall not change a parameter
// value outside that hierarchy", so one that names the top-level module is
// reported rather than applied.
TEST(DefparamSupport, DefparamInGenerateBlockCannotReachOutThroughTheTop) {
  ElabFixture f;
  ElaborateSrc(
      "module leaf #(parameter int P = 1)(); endmodule\n"
      "module top;\n"
      "  leaf u1();\n"
      "  if (1) begin : g\n"
      "    defparam top.u1.P = 7;\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "defparam in a generate block shall not change a "
                            "parameter value outside that block",
                            5, "23.10.1"));
}

}  // namespace

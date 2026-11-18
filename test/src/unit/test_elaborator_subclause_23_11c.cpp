#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_config_unit.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

const RtlirModule* InstanceAt(const RtlirDesign* design,
                              std::string_view path) {
  if (design == nullptr || design->top_modules.empty()) return nullptr;
  const RtlirModule* mod = design->top_modules[0];
  while (mod != nullptr && !path.empty()) {
    size_t dot = path.find('.');
    std::string_view name = path.substr(0, dot);
    const RtlirModule* next = nullptr;
    for (const auto& ch : mod->children) {
      if (ch.inst_name == name) next = ch.resolved;
    }
    mod = next;
    path = dot == std::string_view::npos ? std::string_view{}
                                         : path.substr(dot + 1);
  }
  return mod;
}

bool Holds(const RtlirDesign* design, std::string_view parent,
           std::string_view child) {
  const RtlirModule* mod = InstanceAt(design, parent);
  if (mod == nullptr) return false;
  for (const auto& ch : mod->children) {
    if (ch.inst_name == child) return true;
  }
  return false;
}

constexpr const char* kClash =
    "bind instance name 'p' clashes with existing name in target scope 'cpu'";

constexpr const char* kUnderBind =
    "bind target shall not be a scope created by a bind";

constexpr const char* kIntoInterface = "into interface 'ifc'";

constexpr const char* kBoundParam =
    "a parameter of an instance a bind made is reached by a hierarchical name "
    "where a constant expression is required";

constexpr const char* kBoundMon =
    "module mon #(parameter int W = 4) ();\n"
    "endmodule\n"
    "module cpu;\n"
    "  mon #(.W(2)) q();\n"
    "endmodule\n"
    "bind cpu mon #(.W(8)) r();\n"
    "module top;\n"
    "  cpu c();\n";

TEST(BindTarget, AnInterfaceInstanceTakesAnInterfaceAndACheckerInstance) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface sub; endinterface\n"
      "checker chk; endchecker\n"
      "interface ifc; endinterface\n"
      "module top;\n"
      "  ifc i();\n"
      "endmodule\n"
      "bind top.i sub s();\n"
      "bind top.i chk k();\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_TRUE(Holds(design, "i", "s"));
  EXPECT_TRUE(Holds(design, "i", "k"));
}

TEST(BindTarget, DISABLED_AProgramInstanceIsNoTarget) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module probe; endmodule\n"
      "program prg; endprogram\n"
      "module top;\n"
      "  prg pp();\n"
      "endmodule\n"
      "bind top.pp probe p();\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bind target 'top.pp' is an instance of a program, "
                            "not of a module or interface",
                            6, "23.11"));
  EXPECT_FALSE(Holds(design, "pp", "p"));
}

TEST(BindTarget, DISABLED_ACheckerInstanceIsNoTarget) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module probe; endmodule\n"
      "checker cc_t; endchecker\n"
      "module top;\n"
      "  cc_t cc();\n"
      "endmodule\n"
      "bind top.cc probe p();\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bind target 'top.cc' is an instance of a checker, "
                            "not of a module or interface",
                            6, "23.11"));
  EXPECT_FALSE(Holds(design, "cc", "p"));
}

TEST(BindTarget, AnInstanceNameIsNoTargetScope) {
  ElabFixture f;
  ElaborateSrc(
      "module probe; endmodule\n"
      "module cpu; endmodule\n"
      "module top;\n"
      "  cpu c1();\n"
      "endmodule\n"
      "bind c1 : top.c1 probe p();\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bind target 'c1' is neither a module or interface "
                            "scope nor an instance",
                            6, "23.11"));
}

TEST(BindTarget, DISABLED_ANameThatIsBothAnInstanceAndAModuleBindsTheInstance) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module probe; endmodule\n"
      "module cpu; endmodule\n"
      "module c1; endmodule\n"
      "module top;\n"
      "  cpu c1();\n"
      "  c1 other();\n"
      "  bind c1 probe p();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_TRUE(Holds(design, "c1", "p"));
  EXPECT_FALSE(Holds(design, "other", "p"));
}

TEST(BindTarget, ABoundScopeNamedAsTheTargetScopeIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module inner; endmodule\n"
      "module probe; endmodule\n"
      "module cpu; endmodule\n"
      "module top; cpu c(); endmodule\n"
      "bind cpu probe p();\n"
      "bind probe inner i();\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kUnderBind, 6, "23.11"));
}

TEST(BindTarget, ABoundInstanceInATargetInstanceListIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module inner; endmodule\n"
      "module probe; endmodule\n"
      "module cpu; endmodule\n"
      "module top; cpu c(); endmodule\n"
      "bind cpu probe p();\n"
      "bind probe : top.c.p inner i();\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kUnderBind, 6, "23.11"));
}

TEST(BindTarget, AnUnboundInstanceOfABoundModuleIsATarget) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module inner; endmodule\n"
      "module probe; endmodule\n"
      "module cpu; endmodule\n"
      "module top; cpu c(); probe q(); endmodule\n"
      "bind cpu probe p();\n"
      "bind probe : top.q inner i();\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_TRUE(Holds(design, "q", "i"));
}

TEST(BindInterfaceTarget, AnInterfaceInstanceRefusesAProgram) {
  ElabFixture f;
  ElaborateSrc(
      "program prg; endprogram\n"
      "interface ifc; endinterface\n"
      "module top;\n"
      "  ifc i();\n"
      "endmodule\n"
      "bind top.i prg pr();\n",
      f, "top");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cannot bind non-interface/non-checker 'prg' into interface 'ifc'", 6,
      "23.11"));
}

TEST(BindInterfaceTarget, AnInstanceListOfAnInterfaceRefusesAModule) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module mod; endmodule\n"
      "checker chk; endchecker\n"
      "interface ifc; endinterface\n"
      "module top;\n"
      "  ifc i1();\n"
      "  ifc i2();\n"
      "endmodule\n"
      "bind ifc : top.i1 mod m();\n"
      "bind ifc : top.i2 chk k();\n",
      f, "top");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cannot bind non-interface/non-checker 'mod' into interface 'ifc'", 8,
      "23.11"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kIntoInterface, 9, "23.11"));
  EXPECT_TRUE(Holds(design, "i2", "k"));
}

TEST(BindInterfaceTarget, ABindInAGenerateBlockRefusesAModule) {
  ElabFixture f;
  ElaborateSrc(
      "module mod; endmodule\n"
      "interface ifc; endinterface\n"
      "module top;\n"
      "  ifc i();\n"
      "  if (1) begin : g\n"
      "    bind ifc mod m();\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cannot bind non-interface/non-checker 'mod' into interface 'ifc'", 6,
      "23.11"));
}

TEST(BindPlacement, AnInterfacesGenerateBlockHoldsABind) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module probe; endmodule\n"
      "module cpu; endmodule\n"
      "interface host;\n"
      "  if (1) begin : g\n"
      "    bind cpu probe c();\n"
      "  end\n"
      "  if (0) begin : h\n"
      "    bind cpu probe d();\n"
      "  end\n"
      "endinterface\n"
      "module top;\n"
      "  host hh();\n"
      "  cpu u();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_TRUE(Holds(design, "u", "c"));
  EXPECT_FALSE(Holds(design, "u", "d"));
}

TEST(BindInstantiationKind, DISABLED_AUdpIsNoBindInstantiation) {
  ElabFixture f;
  ElaborateSrc(
      "primitive myudp(output y, input a, input b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    0 1 : 0;\n"
      "    1 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n"
      "module cpu;\n"
      "  wire y, a, b;\n"
      "endmodule\n"
      "module top;\n"
      "  cpu c();\n"
      "endmodule\n"
      "bind cpu myudp u(y, a, b);\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a bind instantiation shall instantiate a module, "
                            "program, interface or checker",
                            15, "23.11"));
}

TEST(BindVisibility, DISABLED_NamesImportedIntoTheCompilationUnitAreNotSeen) {
  ElabFixture f;
  ElaborateSrc(
      "package pk;\n"
      "  int z = 2;\n"
      "  int y = 3;\n"
      "endpackage\n"
      "import pk::*;\n"
      "import pk::y;\n"
      "module mon(input var int v);\n"
      "endmodule\n"
      "module cpu;\n"
      "endmodule\n"
      "module own;\n"
      "  import pk::*;\n"
      "  int a;\n"
      "  initial a = z;\n"
      "endmodule\n"
      "module top;\n"
      "  cpu c();\n"
      "  own o();\n"
      "endmodule\n"
      "bind cpu mon r1(z);\n"
      "bind cpu mon r2(y);\n"
      "bind own mon r3(z);\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "undeclared signal 'z'", 20,
                            "23.11"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "undeclared signal 'y'", 21,
                            "23.11"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "undeclared signal 'z'", 22,
                             "23.11"));
}

TEST(BindVisibility, ANameOnlyTheDirectivesModuleDeclaresIsNotSeen) {
  ElabFixture f;
  ElaborateSrc(
      "module mon(input var int v);\n"
      "endmodule\n"
      "module cpu;\n"
      "endmodule\n"
      "module top;\n"
      "  int z;\n"
      "  cpu c();\n"
      "  bind cpu mon r(z);\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bind port connection 'v' references undeclared "
                            "signal 'z' in target scope 'cpu'",
                            8, "23.11"));
}

TEST(BindParameterReach, DISABLED_AGenerateConditionCannotReadIt) {
  ElabFixture f;
  ElaborateSrc(std::string(kBoundMon) +
                   "  if (c.r.W > 4) begin : g end\n"
                   "  if (c.q.W > 4) begin : h end\n"
                   "endmodule\n",
               f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kBoundParam, 9, "23.11"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kBoundParam, 10, "23.11"));
}

TEST(BindParameterReach, DISABLED_AParameterValueCannotReadIt) {
  ElabFixture f;
  ElaborateSrc(std::string(kBoundMon) +
                   "  localparam int P = c.r.W;\n"
                   "  parameter int Q = c.r.W;\n"
                   "  localparam int R = c.q.W;\n"
                   "endmodule\n",
               f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kBoundParam, 9, "23.11"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kBoundParam, 10, "23.11"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kBoundParam, 11, "23.11"));
}

TEST(BindParameterReach, DISABLED_AParameterOverrideCannotReadIt) {
  ElabFixture f;
  ElaborateSrc(std::string(kBoundMon) +
                   "  mon #(.W(c.r.W)) m();\n"
                   "  mon #(.W(c.q.W)) n();\n"
                   "endmodule\n",
               f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kBoundParam, 9, "23.11"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kBoundParam, 10, "23.11"));
}

TEST(BindParameterReach, DISABLED_AnUnpackedDimensionCannotReadIt) {
  ElabFixture f;
  ElaborateSrc(std::string(kBoundMon) +
                   "  logic v [c.r.W];\n"
                   "  logic w [0:c.r.W-1];\n"
                   "  logic x [c.q.W];\n"
                   "endmodule\n",
               f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kBoundParam, 9, "23.11"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kBoundParam, 10, "23.11"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kBoundParam, 11, "23.11"));
}

TEST(BindTypeOverride, DISABLED_ATypeTheDirectivesScopeCannotSeeIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module chk #(parameter type T = int) ();\n"
      "endmodule\n"
      "module cpu;\n"
      "  typedef logic [6:0] t7;\n"
      "endmodule\n"
      "module top;\n"
      "  cpu c();\n"
      "endmodule\n"
      "bind cpu chk #(.T(t7)) u();\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "type 't7' overriding a type parameter in a bind "
                            "is not visible where the bind is written",
                            9, "23.11"));
}

TEST(BindTypeOverride, DISABLED_ATypeTheTargetCannotSeeIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module chk #(parameter type T = int) ();\n"
      "endmodule\n"
      "module cpu;\n"
      "endmodule\n"
      "module top;\n"
      "  typedef logic [6:0] t7;\n"
      "  cpu c();\n"
      "  bind cpu chk #(.T(t7)) u();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "type 't7' overriding a type parameter in a bind "
                            "is not visible in the bind target 'cpu'",
                            8, "23.11"));
}

TEST(BindTypeOverride, DISABLED_ATypeNamingUnmatchedTypesIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module chk #(parameter type T = int) ();\n"
      "endmodule\n"
      "module cpu;\n"
      "  typedef logic [15:0] t;\n"
      "endmodule\n"
      "module top;\n"
      "  typedef logic [7:0] t;\n"
      "  cpu c();\n"
      "  bind cpu chk #(.T(t)) u();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "type 't' overriding a type parameter in a bind "
                            "names unmatched types where the bind is written "
                            "and in the bind target 'cpu'",
                            9, "23.11"));
}

TEST(BindDefparam, DISABLED_ADefparamCannotReachOutsideTheBoundHierarchy) {
  ElabFixture f;
  ElaborateSrc(
      "module leaf #(parameter W = 1) ();\n"
      "endmodule\n"
      "module c_t;\n"
      "  leaf l();\n"
      "endmodule\n"
      "module probe;\n"
      "  defparam top.c.l.W = 5;\n"
      "endmodule\n"
      "module top;\n"
      "  c_t c();\n"
      "  bind c_t probe p();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "defparam inside a bind instantiation reaches a "
                            "parameter outside that hierarchy",
                            7, "23.11"));
}

TEST(BindNameClash, ANetOfTheTargetClashes) {
  ElabFixture f;
  ElaborateSrc(
      "module probe; endmodule\n"
      "module cpu;\n"
      "  wire p;\n"
      "endmodule\n"
      "module top; cpu c(); endmodule\n"
      "bind cpu probe p();\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kClash, 6, "23.11"));
}

TEST(BindNameClash, DISABLED_AParameterOfTheTargetClashes) {
  ElabFixture f;
  ElaborateSrc(
      "module probe; endmodule\n"
      "module cpu #(parameter p = 1);\n"
      "endmodule\n"
      "module top; cpu c(); endmodule\n"
      "bind cpu probe p();\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kClash, 5, "23.11"));
}

TEST(BindNameClash, DISABLED_ATaskOfTheTargetClashes) {
  ElabFixture f;
  ElaborateSrc(
      "module probe; endmodule\n"
      "module cpu;\n"
      "  task p(); endtask\n"
      "endmodule\n"
      "module top; cpu c(); endmodule\n"
      "bind cpu probe p();\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kClash, 6, "23.11"));
}

TEST(BindNameClash, DISABLED_AFunctionOfTheTargetClashes) {
  ElabFixture f;
  ElaborateSrc(
      "module probe; endmodule\n"
      "module cpu;\n"
      "  function void p(); endfunction\n"
      "endmodule\n"
      "module top; cpu c(); endmodule\n"
      "bind cpu probe p();\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kClash, 6, "23.11"));
}

TEST(BindNameClash, DISABLED_TwoInstancesOfAModuleHoldingABindClash) {
  ElabFixture f;
  ElaborateSrc(
      "module probe; endmodule\n"
      "module cpu; endmodule\n"
      "module holder;\n"
      "  bind cpu probe p();\n"
      "endmodule\n"
      "module top;\n"
      "  cpu c();\n"
      "  holder h1();\n"
      "  holder h2();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kClash, 4, "23.11"));
}

TEST(BindNameClash, AnInstanceBindClashesWithAScopeBind) {
  ElabFixture f;
  ElaborateSrc(
      "module probe; endmodule\n"
      "module cpu; endmodule\n"
      "module top; cpu c(); endmodule\n"
      "bind cpu probe p();\n"
      "bind top.c probe p();\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "bind instance name 'p'", 5,
                            "23.11"));
}

const RtlirModule* BoundCell(RtlirDesign* design, std::string_view inst,
                             std::string_view bound) {
  auto* top = SoleTopModule(design);
  if (top == nullptr) return nullptr;
  for (const auto& ch : top->children) {
    if (ch.inst_name != inst || ch.resolved == nullptr) continue;
    for (const auto& gch : ch.resolved->children) {
      if (gch.inst_name == bound) return gch.resolved;
    }
  }
  return nullptr;
}

TEST(BindLibraryMapping, DISABLED_TheMappingAtTheDirectivePicksTheTargetScope) {
  ConfigUnit u;
  ASSERT_TRUE(
      u.Parse("module chk; endmodule\n"
              "module tgt; endmodule\n"
              "module tgt; endmodule\n"
              "module top;\n"
              "  tgt u1();\n"
              "  tgt u2();\n"
              "  bind tgt chk c();\n"
              "endmodule\n"
              "config cfg;\n"
              "  design top;\n"
              "  default liblist libB libA;\n"
              "  instance top.u1 liblist libA;\n"
              "endconfig\n"));
  u.PlaceModulesInLibraries({"libA", "libA", "libB", "libTop"});
  auto* design = u.ElaborateConfig(0);
  EXPECT_EQ(BoundCell(design, "u1", "c"), nullptr);
  EXPECT_NE(BoundCell(design, "u2", "c"), nullptr);
}

TEST(BindLibraryMapping, TheMappingAtTheDirectivePicksTheBoundCell) {
  ConfigUnit u;
  ASSERT_TRUE(
      u.Parse("module chk; endmodule\n"
              "module chk; endmodule\n"
              "module tgt; endmodule\n"
              "module top;\n"
              "  tgt u();\n"
              "  bind tgt chk c();\n"
              "endmodule\n"
              "config cfg;\n"
              "  design top;\n"
              "  default liblist libA libB;\n"
              "  cell chk liblist libB;\n"
              "endconfig\n"));
  u.PlaceModulesInLibraries({"libA", "libB", "libA", "libTop"});
  const RtlirModule* bound = BoundCell(u.ElaborateConfig(0), "u", "c");
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->library, "libB");
}

TEST(BindLibraryMapping, TheTargetsInstanceClauseIsIgnored) {
  ConfigUnit u;
  ASSERT_TRUE(
      u.Parse("module chk; endmodule\n"
              "module chk; endmodule\n"
              "module tgt; endmodule\n"
              "module top;\n"
              "  tgt u();\n"
              "  bind tgt chk c();\n"
              "endmodule\n"
              "config cfg;\n"
              "  design top;\n"
              "  default liblist libA libB;\n"
              "  instance top.u liblist libB libA;\n"
              "endconfig\n"));
  u.PlaceModulesInLibraries({"libA", "libB", "libA", "libTop"});
  const RtlirModule* bound = BoundCell(u.ElaborateConfig(0), "u", "c");
  ASSERT_NE(bound, nullptr);
  EXPECT_EQ(bound->library, "libA");
}

}  // namespace

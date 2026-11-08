#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

int BoundInChild(const RtlirDesign* design, std::string_view inst,
                 std::string_view bound) {
  int count = 0;
  for (const auto& ch : design->top_modules[0]->children) {
    if (ch.inst_name != inst || ch.resolved == nullptr) continue;
    for (const auto& gch : ch.resolved->children) {
      if (gch.inst_name == bound) ++count;
    }
  }
  return count;
}

TEST(BindDirective, DesignwideInsertionAddsInstanceToEveryInstanceOfTarget) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module probe; endmodule\n"
      "module cpu; endmodule\n"
      "module top;\n"
      "  cpu c1();\n"
      "  cpu c2();\n"
      "endmodule\n"
      "bind cpu probe p();\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto it = design->all_modules.find("cpu");
  ASSERT_NE(it, design->all_modules.end());
  bool found = false;
  for (const auto& ch : it->second->children) {
    if (ch.inst_name == "p" && ch.module_name == "probe") found = true;
  }
  EXPECT_TRUE(found);
}

TEST(BindDirective, DesignwideInsertionIntoInterfaceScope) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker probe_chk; endchecker\n"
      "interface ifc; endinterface\n"
      "module top;\n"
      "  ifc i();\n"
      "endmodule\n"
      "bind ifc probe_chk pc();\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto it = design->all_modules.find("ifc");
  ASSERT_NE(it, design->all_modules.end());
  bool found = false;
  for (const auto& ch : it->second->children)
    if (ch.inst_name == "pc" && ch.module_name == "probe_chk") found = true;
  EXPECT_TRUE(found);
}

TEST(BindDirective, InstanceListRestrictsBindingToListedInstancesOnly) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module probe; endmodule\n"
      "module cpu; endmodule\n"
      "module top;\n"
      "  cpu c1();\n"
      "  cpu c2();\n"
      "  cpu c3();\n"
      "endmodule\n"
      "bind cpu : top.c1, top.c3 probe p();\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  int bound = 0;
  for (const auto& ch : top->children) {
    if (!ch.resolved) continue;
    for (const auto& gch : ch.resolved->children) {
      if (gch.inst_name == "p") ++bound;
    }
  }
  EXPECT_EQ(bound, 2);
}

TEST(BindDirective, FormTwoBindsOnlyToSpecifiedInstance) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module probe; endmodule\n"
      "module cpu; endmodule\n"
      "module top;\n"
      "  cpu c1();\n"
      "  cpu c2();\n"
      "endmodule\n"
      "bind top.c1 probe p();\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  int bound_c1 = 0, bound_c2 = 0;
  for (const auto& ch : top->children) {
    if (!ch.resolved) continue;
    for (const auto& gch : ch.resolved->children) {
      if (gch.inst_name == "p" && ch.inst_name == "c1") ++bound_c1;
      if (gch.inst_name == "p" && ch.inst_name == "c2") ++bound_c2;
    }
  }
  EXPECT_EQ(bound_c1, 1);
  EXPECT_EQ(bound_c2, 0);
}

TEST(BindDirective, InterfaceTargetWithInterfaceInstantiationAllowed) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("interface sub; endinterface\n"
             "interface ifc; endinterface\n"
             "module top;\n"
             "  ifc i();\n"
             "endmodule\n"
             "bind ifc sub s();\n",
             f));
}

TEST(BindDirective, InterfaceTargetWithModuleInstantiationIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module mod; endmodule\n"
      "interface ifc; endinterface\n"
      "module top;\n"
      "  ifc i();\n"
      "endmodule\n"
      "bind ifc mod m();\n",
      f, "top");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cannot bind non-interface/non-checker 'mod' into interface 'ifc'", 6,
      "23.11"));
}

TEST(BindDirective, InterfaceTargetWithProgramInstantiationIsError) {
  ElabFixture f;
  ElaborateSrc(
      "program prg; endprogram\n"
      "interface ifc; endinterface\n"
      "module top;\n"
      "  ifc i();\n"
      "endmodule\n"
      "bind ifc prg pr();\n",
      f, "top");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cannot bind non-interface/non-checker 'prg' into interface 'ifc'", 6,
      "23.11"));
}

TEST(BindDirective, SecondFormInterfaceInstanceRejectsModuleInstantiation) {
  ElabFixture f;
  ElaborateSrc(
      "module mod; endmodule\n"
      "interface ifc; endinterface\n"
      "module top;\n"
      "  ifc i();\n"
      "endmodule\n"
      "bind top.i mod m();\n",
      f, "top");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cannot bind non-interface/non-checker 'mod' into interface 'ifc'", 6,
      "23.11"));
}

TEST(BindDirective, ProgramInstantiationBoundIntoModule) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program probe_prog; endprogram\n"
      "module cpu; endmodule\n"
      "module top; cpu c(); endmodule\n"
      "bind cpu probe_prog pp();\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto it = design->all_modules.find("cpu");
  ASSERT_NE(it, design->all_modules.end());
  bool found = false;
  for (const auto& ch : it->second->children) {
    if (ch.inst_name == "pp" && ch.module_name == "probe_prog") found = true;
  }
  EXPECT_TRUE(found);
}

TEST(BindDirective, InterfaceInstantiationBoundIntoModule) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface probe_if; endinterface\n"
      "module cpu; endmodule\n"
      "module top; cpu c(); endmodule\n"
      "bind cpu probe_if pi();\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto it = design->all_modules.find("cpu");
  ASSERT_NE(it, design->all_modules.end());
  bool found = false;
  for (const auto& ch : it->second->children) {
    if (ch.inst_name == "pi" && ch.module_name == "probe_if") found = true;
  }
  EXPECT_TRUE(found);
}

TEST(BindDirective, CheckerInstantiationBoundIntoModule) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker probe_chk; endchecker\n"
      "module cpu; endmodule\n"
      "module top; cpu c(); endmodule\n"
      "bind cpu probe_chk pc();\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto it = design->all_modules.find("cpu");
  ASSERT_NE(it, design->all_modules.end());
  bool found = false;
  for (const auto& ch : it->second->children) {
    if (ch.inst_name == "pc" && ch.module_name == "probe_chk") found = true;
  }
  EXPECT_TRUE(found);
}

TEST(BindDirective, BoundInstanceActualsResolveInTargetScope) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module probe(input logic x); endmodule\n"
      "module cpu;\n"
      "  logic internal_sig;\n"
      "endmodule\n"
      "module top;\n"
      "  cpu c();\n"
      "endmodule\n"
      "bind cpu probe p(.x(internal_sig));\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(BindDirective, UnitScopeDeclarationsNotVisibleInBindStatement) {
  ElabFixture f;
  ElaborateSrc(
      "logic unit_sig;\n"
      "module probe(input logic x); endmodule\n"
      "module cpu; endmodule\n"
      "module top;\n"
      "  cpu c();\n"
      "endmodule\n"
      "bind cpu probe p(.x(unit_sig));\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bind port connection 'x' references undeclared "
                            "signal 'unit_sig' in target scope 'cpu'",
                            7, "23.11"));
}

TEST(BindDirective, MultipleBindsIntoSameTargetScopeAllowed) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("module probe_a; endmodule\n"
             "module probe_b; endmodule\n"
             "module cpu; endmodule\n"
             "module top;\n"
             "  cpu c();\n"
             "endmodule\n"
             "bind cpu probe_a pa();\n"
             "bind cpu probe_b pb();\n",
             f));
}

TEST(BindDirective, ElaborationOrderOfMultipleBindsIsInsignificant) {
  ElabFixture f1;
  auto* d1 = ElaborateSrc(
      "module probe_a; endmodule\n"
      "module probe_b; endmodule\n"
      "module cpu; endmodule\n"
      "module top; cpu c(); endmodule\n"
      "bind cpu probe_a pa();\n"
      "bind cpu probe_b pb();\n",
      f1, "top");
  ElabFixture f2;
  auto* d2 = ElaborateSrc(
      "module probe_a; endmodule\n"
      "module probe_b; endmodule\n"
      "module cpu; endmodule\n"
      "module top; cpu c(); endmodule\n"
      "bind cpu probe_b pb();\n"
      "bind cpu probe_a pa();\n",
      f2, "top");
  ASSERT_NE(d1, nullptr);
  ASSERT_NE(d2, nullptr);
  EXPECT_FALSE(f1.has_errors);
  EXPECT_FALSE(f2.has_errors);
  auto c1 = d1->all_modules.find("cpu");
  auto c2 = d2->all_modules.find("cpu");
  ASSERT_NE(c1, d1->all_modules.end());
  ASSERT_NE(c2, d2->all_modules.end());
  EXPECT_EQ(c1->second->children.size(), c2->second->children.size());
}

TEST(BindDirective, BoundInstanceNameClashWithExistingNameIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module probe; endmodule\n"
      "module cpu;\n"
      "  logic p;\n"
      "endmodule\n"
      "module top; cpu c(); endmodule\n"
      "bind cpu probe p();\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bind instance name 'p' clashes with existing name "
                            "in target scope 'cpu'",
                            6, "23.11"));
}

TEST(BindDirective, BoundInstanceNameClashWithAnotherBindIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module probe_a; endmodule\n"
      "module probe_b; endmodule\n"
      "module cpu; endmodule\n"
      "module top; cpu c(); endmodule\n"
      "bind cpu probe_a dup();\n"
      "bind cpu probe_b dup();\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bind instance name 'dup' clashes with existing "
                            "name in target scope 'cpu'",
                            6, "23.11"));
}

TEST(BindDirective, BindUnderAnotherBindInstantiationIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module inner; endmodule\n"
      "module probe; endmodule\n"
      "module cpu; endmodule\n"
      "module top; cpu c(); endmodule\n"
      "bind cpu probe p();\n"
      "bind top.c.p inner i();\n",
      f, "top");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "bind target shall not be a scope created by a bind", 6, "23.11"));
}

TEST(BindDirective, UnknownTargetScopeIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module probe; endmodule\n"
      "module top; endmodule\n"
      "bind nonexistent_scope probe p();\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bind target 'nonexistent_scope' is neither a "
                            "module or interface scope nor an instance",
                            3, "23.11"));
}

TEST(BindDirective, ProgramNameAsTargetScopeIsError) {
  ElabFixture f;
  ElaborateSrc(
      "program prg; endprogram\n"
      "module probe; endmodule\n"
      "module top; endmodule\n"
      "bind prg probe pb();\n",
      f, "top");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "bind target 'prg' is neither a module or interface "
                    "scope nor an instance",
                    4, "23.11"));
}

TEST(BindDirective, CheckerNameAsTargetScopeIsError) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk; endchecker\n"
      "module probe; endmodule\n"
      "module top; endmodule\n"
      "bind chk probe pb();\n",
      f, "top");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "bind target 'chk' is neither a module or interface "
                    "scope nor an instance",
                    4, "23.11"));
}

TEST(BindDirective, ModuleNameRemainsValidTargetScope) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module probe; endmodule\n"
      "module cpu; endmodule\n"
      "module top; cpu c(); endmodule\n"
      "bind cpu probe pb();\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto it = design->all_modules.find("cpu");
  ASSERT_NE(it, design->all_modules.end());
  bool found = false;
  for (const auto& ch : it->second->children)
    if (ch.inst_name == "pb" && ch.module_name == "probe") found = true;
  EXPECT_TRUE(found);
}

TEST(BindDirective, SecondFormUnknownInstancePathIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module probe; endmodule\n"
      "module cpu; endmodule\n"
      "module top; cpu c(); endmodule\n"
      "bind top.nonexistent probe p();\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bind target 'top.nonexistent' is neither a module "
                            "or interface scope nor an instance",
                            4, "23.11"));
}

TEST(BindDirective, BindDeclaredInsideModuleAppliesToTarget) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module probe; endmodule\n"
      "module cpu; endmodule\n"
      "module top;\n"
      "  cpu c();\n"
      "  bind cpu probe p();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto it = design->all_modules.find("cpu");
  ASSERT_NE(it, design->all_modules.end());
  bool found = false;
  for (const auto& ch : it->second->children)
    if (ch.inst_name == "p" && ch.module_name == "probe") found = true;
  EXPECT_TRUE(found);
}

TEST(BindDirective, BindDeclaredInsideInterfaceAppliesToTarget) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module probe; endmodule\n"
      "module cpu; endmodule\n"
      "interface ifc;\n"
      "  bind cpu probe p();\n"
      "endinterface\n"
      "module top;\n"
      "  cpu c();\n"
      "  ifc i();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto it = design->all_modules.find("cpu");
  ASSERT_NE(it, design->all_modules.end());
  bool found = false;
  for (const auto& ch : it->second->children)
    if (ch.inst_name == "p" && ch.module_name == "probe") found = true;
  EXPECT_TRUE(found);
}

TEST(BindDirective, BoundInstancePortConnectsToTargetScopeNet) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module probe(input logic x); endmodule\n"
      "module cpu;\n"
      "  wire w;\n"
      "endmodule\n"
      "module top;\n"
      "  cpu c();\n"
      "endmodule\n"
      "bind cpu probe p(.x(w));\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(BindDirective, BoundInstancePortConnectsToTargetScopePort) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module probe(input logic x); endmodule\n"
      "module cpu(input logic pin); endmodule\n"
      "module top;\n"
      "  logic t;\n"
      "  cpu c(.pin(t));\n"
      "endmodule\n"
      "bind cpu probe p(.x(pin));\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(BindDirective, BoundInstanceOrderedPortConnectionResolvesInTargetScope) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module probe(input logic x); endmodule\n"
      "module cpu;\n"
      "  logic internal_sig;\n"
      "endmodule\n"
      "module top;\n"
      "  cpu c();\n"
      "endmodule\n"
      "bind cpu probe p(internal_sig);\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(BindDirective, BoundInstanceNameClashWithChildInstanceIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module sub; endmodule\n"
      "module probe; endmodule\n"
      "module cpu;\n"
      "  sub u1();\n"
      "endmodule\n"
      "module top; cpu c(); endmodule\n"
      "bind cpu probe u1();\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bind instance name 'u1' clashes with existing "
                            "name in target scope 'cpu'",
                            7, "23.11"));
}

int64_t BoundChildParamValue(RtlirDesign* design, std::string_view target_name,
                             std::string_view inst_name,
                             std::string_view param) {
  auto it = design->all_modules.find(target_name);
  if (it == design->all_modules.end()) return -1;
  for (const auto& ch : it->second->children) {
    if (ch.inst_name != inst_name || !ch.resolved) continue;
    for (const auto& p : ch.resolved->params)
      if (p.name == param) return p.resolved_value;
  }
  return -1;
}

TEST(BindDirective, BindInstantiationNamedParameterOverrideTakesEffect) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module probe #(parameter int W = 1); endmodule\n"
      "module cpu; endmodule\n"
      "module top; cpu c(); endmodule\n"
      "bind cpu probe #(.W(8)) p();\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(BoundChildParamValue(design, "cpu", "p", "W"), 8);
}

TEST(BindDirective, BindInstantiationPositionalParameterOverrideTakesEffect) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module probe #(parameter int W = 1); endmodule\n"
      "module cpu; endmodule\n"
      "module top; cpu c(); endmodule\n"
      "bind cpu probe #(8) p();\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(BoundChildParamValue(design, "cpu", "p", "W"), 8);
}

TEST(BindDirective, BindInstantiationOverrideResolvesTargetScopeParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module probe #(parameter int W = 1); endmodule\n"
      "module cpu #(parameter int TW = 5); endmodule\n"
      "module top; cpu c(); endmodule\n"
      "bind cpu probe #(.W(TW)) p();\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(BoundChildParamValue(design, "cpu", "p", "W"), 5);
}

TEST(BindDirective, BindInstantiationOverrideResolvesTargetScopeLocalparam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module probe #(parameter int W = 1); endmodule\n"
      "module cpu;\n"
      "  localparam int LW = 6;\n"
      "endmodule\n"
      "module top; cpu c(); endmodule\n"
      "bind cpu probe #(.W(LW)) p();\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(BoundChildParamValue(design, "cpu", "p", "W"), 6);
}

TEST(BindDirective, BindInstantiationOverrideOfUnknownParameterIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module probe #(parameter int W = 1); endmodule\n"
      "module cpu; endmodule\n"
      "module top; cpu c(); endmodule\n"
      "bind cpu probe #(.NOPE(8)) p();\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module 'probe' has no parameter 'NOPE'", 4,
                            "23.10.2.2"));
}

TEST(BindDirective, BindInstantiationTooManyPositionalOverridesIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module probe; endmodule\n"
      "module cpu; endmodule\n"
      "module top; cpu c(); endmodule\n"
      "bind cpu probe #(8) p();\n",
      f, "top");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "too many positional parameter overrides for module "
                    "'probe': 1 provided, 0 allowed",
                    4, "23.10.2.1"));
}

TEST(BindDirective, TargetIsNeitherScopeNorInstanceNames23_11) {
  ElabFixture f;
  ElaborateSrc(
      "module probe; endmodule\n"
      "module top;\n"
      "endmodule\n"
      "bind nosuch probe p1();\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is neither a module or interface", 4, "23.11"));
}

TEST(BindDirective, TargetInstanceListIsReadFromTheDirectivesModule) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module probe; endmodule\n"
      "module cpu; endmodule\n"
      "module top;\n"
      "  cpu c1();\n"
      "  cpu c2();\n"
      "  cpu c3();\n"
      "  bind cpu: c1, c3 probe p();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(BoundInChild(design, "c1", "p"), 1);
  EXPECT_EQ(BoundInChild(design, "c2", "p"), 0);
  EXPECT_EQ(BoundInChild(design, "c3", "p"), 1);
}

TEST(BindDirective, TargetInstanceIsReadFromTheDirectivesModule) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module probe; endmodule\n"
      "module cpu; endmodule\n"
      "module top;\n"
      "  cpu c1();\n"
      "  cpu c2();\n"
      "  bind c2 probe p();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(BoundInChild(design, "c1", "p"), 0);
  EXPECT_EQ(BoundInChild(design, "c2", "p"), 1);
}

TEST(BindDirective, TargetInstanceListAtUnitScopeIsAFullPath) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module probe; endmodule\n"
      "module cpu; endmodule\n"
      "module top;\n"
      "  cpu c1();\n"
      "  cpu c2();\n"
      "endmodule\n"
      "bind cpu: top.c2 probe p();\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(BoundInChild(design, "c1", "p"), 0);
  EXPECT_EQ(BoundInChild(design, "c2", "p"), 1);
}

TEST(BindDirective, TargetInstanceListEntryNamingNoInstanceIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module probe; endmodule\n"
      "module cpu; endmodule\n"
      "module mem; endmodule\n"
      "module top;\n"
      "  cpu c1();\n"
      "  mem m1();\n"
      "  bind cpu: c1, nosuch, m1 probe p();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bind target instance 'nosuch' is no instance of "
                            "'cpu'",
                            7, "23.11"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bind target instance 'm1' is no instance of 'cpu'",
                            7, "23.11"));
}

TEST(BindDirective, HierarchicalNameReachesABoundInstance) {
  ElabFixture f;
  ElaborateSrc(
      "module m2; int pass = 7; endmodule\n"
      "module sub; endmodule\n"
      "bind sub m2 c();\n"
      "bind top.s1 m2 e();\n"
      "module top;\n"
      "  sub s1();\n"
      "  int x, y, z;\n"
      "  initial begin\n"
      "    x = s1.c.pass;\n"
      "    y = s1.e.pass;\n"
      "    z = s1.d;\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference 's1.d' is unresolved: 'd' "
                            "is not declared in module 'sub'",
                            11, "23.6"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

TEST(BindDirective, BoundModuleReadingItsTargetsVariableByBareNameErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module leaf;\n"
      "  int a = 36;\n"
      "endmodule\n"
      "module mon;\n"
      "  initial #1 $display(\"bnd %0d\", a);\n"
      "endmodule\n"
      "module top;\n"
      "  leaf u();\n"
      "  bind leaf mon m();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'a'", 5,
                            "23.9"));
}

}  // namespace

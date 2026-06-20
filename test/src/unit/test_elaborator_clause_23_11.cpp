#include "fixture_elaborator.h"

using namespace delta;

namespace {

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
  EXPECT_TRUE(
      ElabOk("interface sub; endinterface\n"
             "interface ifc; endinterface\n"
             "module top;\n"
             "  ifc i();\n"
             "endmodule\n"
             "bind ifc sub s();\n"));
}

TEST(BindDirective, InterfaceTargetWithCheckerInstantiationAllowed) {
  EXPECT_TRUE(
      ElabOk("checker chk; endchecker\n"
             "interface ifc; endinterface\n"
             "module top;\n"
             "  ifc i();\n"
             "endmodule\n"
             "bind ifc chk c();\n"));
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
}

// Footnote 4 also governs the second bind form: when the bind_target_instance
// resolves to an interface instance, the bind_instantiation must still be an
// interface or checker instantiation, so binding a module there is an error.
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
  EXPECT_TRUE(f.has_errors);
}

// bind_instantiation may be a program_instantiation: a program bound into a
// module becomes part of that module, mirroring the standard's fpu example.
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

// bind_instantiation may be an interface_instantiation bound into a module
// scope, as in the standard's interface-into-cr_unit example.
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

// bind_instantiation may be a checker_instantiation bound into a module scope.
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
  EXPECT_TRUE(f.has_errors);
}

TEST(BindDirective, MultipleBindsIntoSameTargetScopeAllowed) {
  EXPECT_TRUE(
      ElabOk("module probe_a; endmodule\n"
             "module probe_b; endmodule\n"
             "module cpu; endmodule\n"
             "module top;\n"
             "  cpu c();\n"
             "endmodule\n"
             "bind cpu probe_a pa();\n"
             "bind cpu probe_b pb();\n"));
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
}

// A bind_target_scope must name a module or interface; a bare target naming
// neither a known scope nor any instance denotes nothing bindable.
TEST(BindDirective, UnknownTargetScopeIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module probe; endmodule\n"
      "module top; endmodule\n"
      "bind nonexistent_scope probe p();\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

// A bind_target_instance must resolve to an instance; a hierarchical path that
// matches no instance in the design is an error.
TEST(BindDirective, SecondFormUnknownInstancePathIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module probe; endmodule\n"
      "module cpu; endmodule\n"
      "module top; cpu c(); endmodule\n"
      "bind top.nonexistent probe p();\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

}  // namespace

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

// bind_target_scope may be an interface_identifier, and with no
// bind_target_instance_list the instantiation is inserted designwide into every
// instance of that interface. Distinct input form from the module-scope case:
// the target is an interface and (per footnote 4) the bound thing is a checker.
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
  EXPECT_TRUE(
      ElabOk("interface sub; endinterface\n"
             "interface ifc; endinterface\n"
             "module top;\n"
             "  ifc i();\n"
             "endmodule\n"
             "bind ifc sub s();\n"));
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

// §23.11: a bind_target_scope shall be a module or an interface. A program name
// is not a legal target scope, so a bind naming a program as its scope denotes
// nothing bindable and is an error even though the program is a known design
// element that could otherwise be a bind_instantiation.
TEST(BindDirective, ProgramNameAsTargetScopeIsError) {
  ElabFixture f;
  ElaborateSrc(
      "program prg; endprogram\n"
      "module probe; endmodule\n"
      "module top; endmodule\n"
      "bind prg probe pb();\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

// §23.11 companion to the program case: a checker name is likewise not a legal
// bind_target_scope, so binding into a checker scope is an error.
TEST(BindDirective, CheckerNameAsTargetScopeIsError) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk; endchecker\n"
      "module probe; endmodule\n"
      "module top; endmodule\n"
      "bind chk probe pb();\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

// The scope-kind restriction narrows only programs and checkers: a plain module
// name remains a valid bind_target_scope and still binds designwide, so this
// accepting companion guards against over-rejecting.
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

// §23.11: a bind directive may be written inside a module scope (not only at
// compilation-unit scope). Such a nested directive is still collected and still
// binds designwide into its named target, so the bound instance appears in the
// target regardless of where the directive was written.
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

// Companion placement: a bind directive written inside an interface scope is
// likewise collected and applied to its target, exercising the interface-scope
// collection path distinct from the module- and compilation-unit-scope ones.
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

// §23.11: a bound instance's actual ports resolve against the target scope. A
// prior test covers a variable actual; this covers a net (wire) declared in the
// target, a distinct declaration form the resolution must admit.
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

// §23.11: a bound instance's actual may name a port of the target scope, the
// third declaration form (alongside variables and nets) the target-scope
// resolution admits.
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

// §23.11: port associations in a bind_instantiation may be positional, not only
// named. The ordered actual binds by position and still resolves against the
// target scope, exercising the ordered-connection path.
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

// §23.11 (via §3.13): the module name space of the target scope includes
// instance names, so a bound instance whose name collides with an existing
// child instance in the target is an error — distinct from a collision with a
// variable, which a prior test covers.
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
  EXPECT_TRUE(f.has_errors);
}

// Locate the bound child instance `inst_name` inside the elaborated target
// module `target_name`, and return the resolved value of its parameter `param`.
// Returns -1 when the instance, its resolution, or the parameter is missing so
// a caller's positive expectation fails loudly rather than silently passing.
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

// §23.11: parameter associations written on a bind_instantiation take effect. A
// named override with a literal value must reach the bound instance's resolved
// parameters, driven end-to-end through parse and elaborate.
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

// Positional parameter overrides on a bind_instantiation follow a distinct
// resolution path from named ones and must likewise take effect.
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

// §23.11: the bind actuals refer to objects from the viewpoint of the bind
// target. A parameter override whose value is a parameter of the target scope
// must resolve against the target's parameter environment (a constant-form
// distinct from a literal).
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

// Companion constant-form: the override value may be a localparam of the target
// scope, resolved the same way through the target's parameter environment.
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

// Negative form of the named override: naming a parameter the bound module does
// not declare is an error, now reachable through the bind path.
TEST(BindDirective, BindInstantiationOverrideOfUnknownParameterIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module probe #(parameter int W = 1); endmodule\n"
      "module cpu; endmodule\n"
      "module top; cpu c(); endmodule\n"
      "bind cpu probe #(.NOPE(8)) p();\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

// Negative form of the positional override: supplying more positional overrides
// than the bound module has overridable parameters is an error.
TEST(BindDirective, BindInstantiationTooManyPositionalOverridesIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module probe; endmodule\n"
      "module cpu; endmodule\n"
      "module top; cpu c(); endmodule\n"
      "bind cpu probe #(8) p();\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

}  // namespace

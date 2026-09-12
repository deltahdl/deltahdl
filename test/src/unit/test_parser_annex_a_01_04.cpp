#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ElaborationSeverityTask, ElabSeverityFatal) {
  auto r = Parse(
      "module m;\n"
      "  $fatal(1, \"assertion failed\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kElabSystemTask);
}

TEST(ElaborationSeverityTask, ElabSeverityAllForms) {
  auto r = Parse(
      "module m;\n"
      "  $fatal;\n"
      "  $error(\"err\");\n"
      "  $warning(\"warn\");\n"
      "  $info;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 4u);
  for (size_t i = 0; i < 4; ++i) {
    EXPECT_EQ(r.cu->modules[0]->items[i]->kind,
              ModuleItemKind::kElabSystemTask);
  }
}

TEST(ElaborationSeverityTask, ProgramElabSeverityTask) {
  auto r = Parse(
      "program prg;\n"
      "  $info(\"program loaded\");\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kElabSystemTask));
}

TEST(ElaborationSeverityTask, FatalFinishNumberZero) {
  auto r = Parse(
      "module m;\n"
      "  $fatal(0);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kElabSystemTask));
}

TEST(ElaborationSeverityTask, FatalFinishNumberTwo) {
  auto r = Parse(
      "module m;\n"
      "  $fatal(2);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kElabSystemTask));
}

TEST(ElaborationSeverityTask, FatalFinishNumberOnly) {
  auto r = Parse(
      "module m;\n"
      "  $fatal(1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kElabSystemTask));
}

TEST(ElaborationSeverityTask, ErrorNoArgs) {
  auto r = Parse(
      "module m;\n"
      "  $error;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kElabSystemTask));
}

TEST(ElaborationSeverityTask, FatalWithFinishNumberAndMultipleArgs) {
  auto r = Parse(
      "module m;\n"
      "  $fatal(2, \"fmt %0d %0d\", 1, 2);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kElabSystemTask));
}

TEST(BindDirective, BindDirectiveParameterized) {
  auto r = Parse("bind target_mod my_checker #(8) chk_i(.clk(clk));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  auto* inst = r.cu->bind_directives[0]->instantiation;
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->inst_params.size(), 1u);
}

TEST(BindDirective, BindDirectiveHasSourceLoc) {
  auto r = Parse("bind target_mod chk chk_i(.a(s));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_NE(r.cu->bind_directives[0]->loc.line, 0u);
}

TEST(BindDirective, MultipleBindDirectives) {
  auto r = Parse(
      "bind mod1 chk1 c1(.a(s));\n"
      "bind mod2 chk2 c2(.a(s));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 2u);
  EXPECT_EQ(r.cu->bind_directives[0]->target.path, "mod1");
  EXPECT_EQ(r.cu->bind_directives[1]->target.path, "mod2");
}

TEST(BindDirective, BindMixedWithOtherDescriptions) {
  auto r = Parse(
      "module m; endmodule\n"
      "bind m checker_mod chk_i(.a(sig));\n"
      "package p; endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_EQ(r.cu->packages.size(), 1u);
}

TEST(BindDirective, BindDirectiveWithAttributes) {
  auto r = Parse(
      "module m; endmodule\n"
      "module checker_m; endmodule\n"
      "(* synthesis *) bind m checker_m inst(.*);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->bind_directives.size(), 1u);
}

TEST(BindDirective, BindTargetInterfaceScope) {
  auto r = Parse(
      "interface ifc; endinterface\n"
      "bind ifc checker_mod chk_i(.a(sig));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives[0]->target.path, "ifc");
}

TEST(BindDirective, BindEmptyPortList) {
  auto r = Parse("bind target_mod checker_mod chk_i();\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
}

TEST(BindDirective, BindWithWildcardPorts) {
  auto r = Parse("bind target_mod checker_mod chk_i(.*);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
}

TEST(BindDirective, BindTargetInstanceWithBitSelect) {
  auto r = Parse("bind target[0] checker_mod chk_i(.a(sig));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives[0]->target.path, "target");
  ASSERT_EQ(r.cu->bind_directives[0]->target.segments.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives[0]->target.segments[0].selects.size(), 1u);
}

TEST(BindDirective, BindTargetHierarchicalWithBitSelect) {
  auto r = Parse("bind top.dut[2] checker_mod chk(.a(sig));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives[0]->target.path, "top.dut");
  ASSERT_EQ(r.cu->bind_directives[0]->target.segments.size(), 2u);
  EXPECT_TRUE(r.cu->bind_directives[0]->target.segments[0].selects.empty());
  EXPECT_EQ(r.cu->bind_directives[0]->target.segments[1].selects.size(), 1u);
}

TEST(BindDirective, BindInstanceListWithBitSelects) {
  auto r = Parse("bind dut : u[0], v[1] chk chk_i(.clk(clk));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  const auto& instances = r.cu->bind_directives[0]->target_instances;
  ASSERT_EQ(instances.size(), 2u);
  ASSERT_EQ(instances[0].segments.size(), 1u);
  EXPECT_EQ(instances[0].segments[0].selects.size(), 1u);
  ASSERT_EQ(instances[1].segments.size(), 1u);
  EXPECT_EQ(instances[1].segments[0].selects.size(), 1u);
}

TEST(BindDirective, BindTargetWithoutBitSelect) {
  auto r = Parse("bind target_mod checker_mod chk_i(.a(sig));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  ASSERT_EQ(r.cu->bind_directives[0]->target.segments.size(), 1u);
  EXPECT_TRUE(r.cu->bind_directives[0]->target.segments[0].selects.empty());
}

TEST(BindDirective, ErrorBindMissingTarget) {
  auto r = Parse("bind ;\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got ';'", 1, "23.11"));
}

// bind_target_instance ::= hierarchical_identifier constant_bit_select, and
// A.9.3's hierarchical_identifier, `[ $root . ] { identifier
// constant_bit_select . } identifier`, lets a select stand on any identifier of
// the path, not only its last: the instance inside a generate loop's block is
// spelled `top.g[0].u`.
TEST(BindDirective, TargetInstanceSelectInsideHierarchicalIdentifier) {
  auto r = Parse("bind top.g[0].u chk c();\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  const auto& target = r.cu->bind_directives[0]->target;
  EXPECT_EQ(target.path, "top.g.u");
  ASSERT_EQ(target.segments.size(), 3u);
  EXPECT_EQ(target.segments[0].name, "top");
  EXPECT_TRUE(target.segments[0].selects.empty());
  EXPECT_EQ(target.segments[1].name, "g");
  EXPECT_EQ(target.segments[1].selects.size(), 1u);
  EXPECT_EQ(target.segments[2].name, "u");
  EXPECT_TRUE(target.segments[2].selects.empty());
  EXPECT_TRUE(r.cu->bind_directives[0]->target_instances.empty());
}

// constant_bit_select ::= { [ constant_expression ] } -- zero or more, so an
// element of a two-dimensional instance array carries two.
TEST(BindDirective, TargetInstanceCarriesEverySelect) {
  auto r = Parse("bind top.u[0][1] chk c();\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  const auto& target = r.cu->bind_directives[0]->target;
  EXPECT_EQ(target.path, "top.u");
  ASSERT_EQ(target.segments.size(), 2u);
  EXPECT_EQ(target.segments[1].selects.size(), 2u);
}

// A.9.3 opens hierarchical_identifier with an optional `$root .`, which names
// the same instance as the path without it and is left out of the recorded
// path.
TEST(BindDirective, RootedTargetInstance) {
  auto r = Parse("bind $root.top.c1 chk c();\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  const auto& target = r.cu->bind_directives[0]->target;
  EXPECT_TRUE(target.from_root);
  EXPECT_EQ(target.path, "top.c1");
  ASSERT_EQ(target.segments.size(), 2u);
}

// Each bind_target_instance of the first form's list is read by the same
// production, so the selects inside its path are held as the second form's.
TEST(BindDirective, TargetInstanceListEntrySelectInsideHierarchicalIdentifier) {
  auto r = Parse("bind cpu : top.g[0].u, top.v[1][2] chk c();\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives[0]->target.path, "cpu");
  const auto& instances = r.cu->bind_directives[0]->target_instances;
  ASSERT_EQ(instances.size(), 2u);
  EXPECT_EQ(instances[0].path, "top.g.u");
  ASSERT_EQ(instances[0].segments.size(), 3u);
  EXPECT_EQ(instances[0].segments[1].selects.size(), 1u);
  EXPECT_EQ(instances[1].path, "top.v");
  ASSERT_EQ(instances[1].segments.size(), 2u);
  EXPECT_EQ(instances[1].segments[1].selects.size(), 2u);
}

// bind_target_scope ::= module_identifier | interface_identifier, one name;
// §23.11 has it name the module or interface whose instances the list after
// the ':' narrows. An instance path in its place names one instance, and the
// list then narrows nothing, so it is reported at the target; the list and the
// instantiation are still read, so the directive ends at its own ';'.
TEST(BindDirective, ErrorHierarchicalTargetScopeIsRejected) {
  auto r = Parse("bind top.dut : u1 chk c();\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "bind target scope is a module or interface identifier", 1,
      "A.1.4"));
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  ASSERT_EQ(r.cu->bind_directives[0]->target_instances.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives[0]->target_instances[0].path, "u1");
  EXPECT_NE(r.cu->bind_directives[0]->instantiation, nullptr);
}

// A select on the scope's name makes it an element of an instance array, a
// bind_target_instance rather than a bind_target_scope.
TEST(BindDirective, ErrorSelectedTargetScopeIsRejected) {
  auto r = Parse("bind dut[0] : u1 chk c();\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "bind target scope is a module or interface identifier", 1,
      "A.1.4"));
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_NE(r.cu->bind_directives[0]->instantiation, nullptr);
}

// `$root .` opens a hierarchical_identifier and so an instance path; a
// module_identifier carries no such prefix.
TEST(BindDirective, ErrorRootedTargetScopeIsRejected) {
  auto r = Parse("bind $root.cpu : top.c1 chk c();\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "bind target scope is a module or interface identifier", 1,
      "A.1.4"));
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_NE(r.cu->bind_directives[0]->instantiation, nullptr);
}

// The first form with a single module name and the second form with a single
// instance name are spelled alike up to the ':', so a plain name before it is
// held to nothing; §23.11 settles which the name is at elaboration.
TEST(BindDirective, PlainTargetScopeBeforeInstanceListIsAccepted) {
  auto r = Parse("bind cpu : top.c1 chk c();\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives[0]->target.path, "cpu");
  EXPECT_FALSE(r.cu->bind_directives[0]->target.from_root);
}

// --- module_common_item ---
// module_common_item enumerates the constructs shared by modules, interfaces,
// programs, and checkers. These tests observe that the shared module-item parse
// path accepts each alternative inside a module body and records the matching
// item kind. The same path is reused for interface bodies in A.1.6.

TEST(ModuleCommonItem, ContinuousAssignAndProceduralConstructs) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  assign w = a;\n"
      "  initial x = 0;\n"
      "  final y = 1;\n"
      "  always @(*) z = w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto& items = r.cu->modules[0]->items;
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kContAssign));
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kInitialBlock));
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kFinalBlock));
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kAlwaysBlock));
}

TEST(ModuleCommonItem, NetAlias) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  alias a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kAlias));
}

TEST(ModuleCommonItem, LoopAndConditionalGenerateConstructs) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 2; i = i + 1) begin : g end\n"
      "  if (1) begin : c end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto& items = r.cu->modules[0]->items;
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kGenerateFor));
  EXPECT_TRUE(HasItemOfKind(items, ModuleItemKind::kGenerateIf));
}

TEST(ModuleCommonItem, AssertionItem) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty));
}

// --- module_or_generate_item_declaration ---

TEST(ModuleOrGenerateItemDecl, ClockingAndDefaultClocking) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk); endclocking\n"
      "  default clocking cb;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto& items = r.cu->modules[0]->items;
  EXPECT_EQ(CountItemsByKind(items, ModuleItemKind::kClockingBlock), 2u);
  bool saw_default = false;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kClockingBlock &&
        item->is_default_clocking) {
      saw_default = true;
    }
  }
  EXPECT_TRUE(saw_default);
}

TEST(ModuleOrGenerateItemDecl, DefaultDisableIff) {
  auto r = Parse(
      "module m;\n"
      "  default disable iff rst;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r.cu->modules[0]->items,
                              ModuleItemKind::kDefaultDisableIff);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->init_expr, nullptr);
}

// --- module_or_generate_item: parameter_override and gate_instantiation ---

TEST(ModuleOrGenerateItem, ParameterOverrideDefparam) {
  auto r = Parse(
      "module m;\n"
      "  defparam u.p = 4;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kDefparam));
}

TEST(ModuleOrGenerateItem, GateInstantiation) {
  auto r = Parse(
      "module m;\n"
      "  and g1(o, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kGateInst));
}

// --- non_port_module_item ---

TEST(NonPortModuleItem, SpecparamDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  specparam delay = 10;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kSpecparam));
}

TEST(NonPortModuleItem, NestedModuleDeclaration) {
  auto r = Parse(
      "module outer;\n"
      "  module inner; endmodule\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r.cu->modules[0]->items,
                              ModuleItemKind::kNestedModuleDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->nested_module_decl, nullptr);
  EXPECT_EQ(item->nested_module_decl->name, "inner");
}

// --- module_item: port_declaration ; alongside a non_port_module_item ---

TEST(ModuleItem, NonAnsiPortDeclarationAndNonPortItem) {
  auto r = Parse(
      "module m(a, b);\n"
      "  input a;\n"
      "  output b;\n"
      "  assign b = a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 2u);
  EXPECT_EQ(mod->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mod->ports[1].direction, Direction::kOutput);
  EXPECT_TRUE(HasItemOfKind(mod->items, ModuleItemKind::kContAssign));
}

// module_common_item lists interface_instantiation and program_instantiation,
// and module_or_generate_item lists module_instantiation. All three share one
// instantiation syntax (the module/interface/program distinction is resolved at
// elaboration), so the parser records them uniformly as a module instance.
// udp_instantiation is the same syntax and is distinguished only when a UDP of
// that name is in scope (observed under A.5.4).
TEST(ModuleOrGenerateItem, InstantiationItem) {
  auto r = Parse(
      "module m;\n"
      "  sub u0(.a(x), .b(y));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kModuleInst));
}

// --- module_or_generate_item_declaration: remaining named alternatives ---

TEST(ModuleOrGenerateItemDecl, GenvarDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByName(r.cu->modules[0]->items, "i");
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
}

// package_or_generate_item_declaration is one of the alternatives; observe that
// a representative package_or_generate_item (a parameter declaration) is
// accepted as a module item.
TEST(ModuleOrGenerateItemDecl, PackageOrGenerateItemDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  parameter P = 4;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kParamDecl));
}

// --- non_port_module_item: remaining named alternatives ---

TEST(NonPortModuleItem, GenerateRegion) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    if (1) begin : g end\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kGenerateIf));
}

TEST(NonPortModuleItem, SpecifyBlock) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kSpecifyBlock));
}

TEST(NonPortModuleItem, TimeunitsDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->has_timeunit);
  EXPECT_TRUE(r.cu->modules[0]->has_timeprecision);
}

TEST(NonPortModuleItem, NestedProgramAndInterfaceDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  program prg; endprogram\n"
      "  interface ifc; endinterface\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool saw_program = false, saw_interface = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kNestedModuleDecl) continue;
    if (!item->nested_module_decl) continue;
    if (item->nested_module_decl->decl_kind == ModuleDeclKind::kProgram)
      saw_program = true;
    if (item->nested_module_decl->decl_kind == ModuleDeclKind::kInterface)
      saw_interface = true;
  }
  EXPECT_TRUE(saw_program);
  EXPECT_TRUE(saw_interface);
}

// --- error conditions / edge cases ---

// elaboration_severity_system_task ends in a required `;`. Omitting it is a
// parse error.
TEST(ElaborationSeverityTask, SeverityTaskMissingSemicolonRejected) {
  auto r = Parse(
      "module m;\n"
      "  $info(\"x\")\n"
      "endmodule\n");
  // `endmodule` is the token standing where the ';' was wanted on line 3.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endmodule'", 3, "20.10.1"));
}

// parameter_override ::= defparam list_of_defparam_assignments ; — the trailing
// `;` is required.
TEST(ModuleOrGenerateItem, ParameterOverrideMissingSemicolonRejected) {
  auto r = Parse(
      "module m;\n"
      "  defparam u.p = 4\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endmodule'", 3, "23.10.1"));
}

// module_or_generate_item_declaration's `default disable iff
// expression_or_dist` form requires the `iff` keyword after `default disable`.
TEST(ModuleOrGenerateItemDecl, DefaultDisableMissingIffRejected) {
  auto r = Parse(
      "module m;\n"
      "  default disable rst;\n"
      "endmodule\n");
  // §16.15 owns `default disable iff`, so the missing `iff` is reported there
  // rather than under A.1.4's module_or_generate_item_declaration.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'iff', got identifier", 2, "16.15"));
}

}  // namespace

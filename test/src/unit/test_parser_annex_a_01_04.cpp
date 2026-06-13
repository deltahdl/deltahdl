#include "fixture_parser.h"
#include "helpers_parser_verify.h"

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
  EXPECT_EQ(r.cu->bind_directives[0]->target, "mod1");
  EXPECT_EQ(r.cu->bind_directives[1]->target, "mod2");
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
  EXPECT_EQ(r.cu->bind_directives[0]->target, "ifc");
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
  EXPECT_EQ(r.cu->bind_directives[0]->target, "target");
  EXPECT_NE(r.cu->bind_directives[0]->target_bit_select, nullptr);
}

TEST(BindDirective, BindTargetHierarchicalWithBitSelect) {
  auto r = Parse("bind top.dut[2] checker_mod chk(.a(sig));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives[0]->target, "top.dut");
  EXPECT_NE(r.cu->bind_directives[0]->target_bit_select, nullptr);
}

TEST(BindDirective, BindInstanceListWithBitSelects) {
  auto r = Parse("bind dut : u[0], v[1] chk chk_i(.clk(clk));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  ASSERT_EQ(r.cu->bind_directives[0]->target_instances.size(), 2u);
  ASSERT_EQ(r.cu->bind_directives[0]->target_instance_bit_selects.size(), 2u);
  EXPECT_NE(r.cu->bind_directives[0]->target_instance_bit_selects[0], nullptr);
  EXPECT_NE(r.cu->bind_directives[0]->target_instance_bit_selects[1], nullptr);
}

TEST(BindDirective, BindTargetWithoutBitSelect) {
  auto r = Parse("bind target_mod checker_mod chk_i(.a(sig));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives[0]->target_bit_select, nullptr);
}

TEST(BindDirective, ErrorBindMissingTarget) {
  auto r = Parse("bind ;\n");
  EXPECT_TRUE(r.has_errors);
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
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kDefaultDisableIff);
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
  EXPECT_TRUE(HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kDefparam));
}

TEST(ModuleOrGenerateItem, GateInstantiation) {
  auto r = Parse(
      "module m;\n"
      "  and g1(o, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kGateInst));
}

// --- non_port_module_item ---

TEST(NonPortModuleItem, SpecparamDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  specparam delay = 10;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kSpecparam));
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
  EXPECT_TRUE(HasItemOfKind(r.cu->modules[0]->items,
                            ModuleItemKind::kModuleInst));
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
  EXPECT_TRUE(HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kParamDecl));
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
  EXPECT_TRUE(HasItemOfKind(r.cu->modules[0]->items,
                            ModuleItemKind::kGenerateIf));
}

TEST(NonPortModuleItem, SpecifyBlock) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(r.cu->modules[0]->items,
                            ModuleItemKind::kSpecifyBlock));
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
  EXPECT_TRUE(r.has_errors);
}

// parameter_override ::= defparam list_of_defparam_assignments ; — the trailing
// `;` is required.
TEST(ModuleOrGenerateItem, ParameterOverrideMissingSemicolonRejected) {
  auto r = Parse(
      "module m;\n"
      "  defparam u.p = 4\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// module_or_generate_item_declaration's `default disable iff expression_or_dist`
// form requires the `iff` keyword after `default disable`.
TEST(ModuleOrGenerateItemDecl, DefaultDisableMissingIffRejected) {
  auto r = Parse(
      "module m;\n"
      "  default disable rst;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}

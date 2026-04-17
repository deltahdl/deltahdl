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

TEST(ElaborationSeverityTask, WarningWithArgs) {
  auto r = Parse(
      "module m;\n"
      "  $warning(\"potential issue\");\n"
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

}  // namespace

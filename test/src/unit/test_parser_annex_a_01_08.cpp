#include <gtest/gtest.h>

#include <cstddef>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST(CheckerItemsParsing, CheckerPortListDetailed) {
  auto r = Parse(
      "checker chk(input logic clk, output bit valid);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  auto* chk = r.cu->checkers[0];
  EXPECT_EQ(chk->name, "chk");
  EXPECT_EQ(chk->decl_kind, ModuleDeclKind::kChecker);
  ASSERT_EQ(chk->ports.size(), 2u);
  EXPECT_EQ(chk->ports[0].direction, Direction::kInput);
  EXPECT_EQ(chk->ports[0].name, "clk");
  EXPECT_EQ(chk->ports[1].direction, Direction::kOutput);
  EXPECT_EQ(chk->ports[1].name, "valid");
}

TEST(CheckerItemsParsing, CheckerPortWithAttribute) {
  auto r = Parse(
      "checker chk((* mark *) input logic clk);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_EQ(r.cu->checkers[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->ports[0].name, "clk");
  EXPECT_EQ(r.cu->checkers[0]->ports[0].direction, Direction::kInput);
}

TEST(CheckerItemsParsing, CheckerPortWithArrayDimension) {
  auto r = Parse(
      "checker chk(input logic data [3:0]);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_EQ(r.cu->checkers[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->ports[0].name, "data");
  EXPECT_FALSE(r.cu->checkers[0]->ports[0].unpacked_dims.empty());
}

TEST(CheckerItemsParsing, CheckerPortDefaultValue) {
  auto r = Parse(
      "checker chk(input logic clk = 1'b0);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_EQ(r.cu->checkers[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->ports[0].direction, Direction::kInput);
  EXPECT_EQ(r.cu->checkers[0]->ports[0].name, "clk");
  EXPECT_NE(r.cu->checkers[0]->ports[0].default_value, nullptr);
}

TEST(CheckerItemsParsing, CheckerPortImplicitDirection) {
  auto r = Parse(
      "checker chk(logic sig);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_EQ(r.cu->checkers[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->ports[0].name, "sig");
}

TEST(CheckerItemsParsing, CheckerNoPorts) {
  auto r = Parse(
      "checker no_ports;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_TRUE(r.cu->checkers[0]->ports.empty());
}

TEST(CheckerItemsParsing, CheckerEmptyParenPorts) {
  auto r = Parse(
      "checker empty_parens();\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_TRUE(r.cu->checkers[0]->ports.empty());
}

TEST(CheckerItemsParsing, CheckerInitialAlwaysFinal) {
  auto r = Parse(
      "checker chk;\n"
      "  initial begin end\n"
      "  always @(posedge clk) x <= 1;\n"
      "  final begin end\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  auto& items = r.cu->checkers[0]->items;
  ASSERT_GE(items.size(), 3u);
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kInitialBlock));
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kAlwaysBlock));
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kFinalBlock));
}

TEST(CheckerItemsParsing, CheckerAssertionItemKind) {
  auto r = Parse(
      "checker chk;\n"
      "  assert property (@(posedge clk) a |-> b);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_GE(r.cu->checkers[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->items[0]->kind, ModuleItemKind::kAssertProperty);
}

TEST(CheckerItemsParsing, CheckerContAssignItemKind) {
  auto r = Parse(
      "checker chk;\n"
      "  assign a = b;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_GE(r.cu->checkers[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->items[0]->kind, ModuleItemKind::kContAssign);
}

TEST(CheckerItemsParsing, CheckerRandDataDeclItemKind) {
  auto r = Parse(
      "checker chk;\n"
      "  rand bit [3:0] val;\n"
      "  logic [7:0] data;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_GE(r.cu->checkers[0]->items.size(), 2u);
  EXPECT_EQ(r.cu->checkers[0]->items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_TRUE(r.cu->checkers[0]->items[0]->is_rand);
  EXPECT_EQ(r.cu->checkers[0]->items[1]->kind, ModuleItemKind::kVarDecl);
  EXPECT_FALSE(r.cu->checkers[0]->items[1]->is_rand);
}

TEST(CheckerItemsParsing, CheckerFuncDeclAutomatic) {
  auto r = Parse(
      "checker chk;\n"
      "  function automatic int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_GE(r.cu->checkers[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->items[0]->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(r.cu->checkers[0]->items[0]->name, "add");
}

TEST(CheckerItemsParsing, CheckerNestedCheckerDeclaration) {
  auto r = Parse(
      "checker outer;\n"
      "  checker inner;\n"
      "  endchecker\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "outer");
  EXPECT_FALSE(r.cu->checkers[0]->items.empty());
}

TEST(CheckerItemsParsing, CheckerPropertyDecl) {
  auto r = Parse(
      "checker prop_check(input logic clk, input logic a, input logic b);\n"
      "  property p1;\n"
      "    a |-> b;\n"
      "  endproperty\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kPropertyDecl));
}

TEST(CheckerItemsParsing, CheckerCovergroup) {
  auto r = Parse(
      "checker cov_check(input logic clk, input logic x);\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kCovergroupDecl));
}

TEST(CheckerItemsParsing, CheckerGenvarDeclItemKind) {
  auto r = Parse(
      "checker chk;\n"
      "  genvar i;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_GE(r.cu->checkers[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(r.cu->checkers[0]->items[0]->name, "i");
}

TEST(CheckerItemsParsing, CheckerClocking) {
  auto r = Parse(
      "checker my_chk;\n"
      "  clocking cb @(posedge clk);\n"
      "  endclocking\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CheckerItemsParsing, CheckerDefaultClocking) {
  auto r = Parse(
      "checker my_chk;\n"
      "  clocking cb @(posedge clk);\n"
      "  endclocking\n"
      "  default clocking cb;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CheckerItemsParsing, CheckerDefaultDisableIff) {
  auto r = Parse(
      "checker my_chk;\n"
      "  default disable iff rst;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CheckerItemsParsing, CheckerNullItem) {
  auto r = Parse(
      "checker my_chk;\n"
      "  ;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CheckerItemsParsing, CheckerGenFor) {
  auto r = Parse(
      "checker my_chk;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; i = i + 1) begin : gen\n"
      "    wire w;\n"
      "  end\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kGenerateFor));
}

TEST(CheckerItemsParsing, GenerateItemInChecker) {
  auto r = Parse(
      "checker my_chk;\n"
      "  if (W > 0)\n"
      "    wire a;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  bool found_if = false;
  for (auto* item : r.cu->checkers[0]->items) {
    if (item->kind == ModuleItemKind::kGenerateIf) found_if = true;
  }
  EXPECT_TRUE(found_if);
}

TEST(CheckerItemsParsing, CheckerCaseGenerate) {
  auto r = Parse(
      "checker chk;\n"
      "  case (MODE)\n"
      "    0: wire a;\n"
      "    1: wire b;\n"
      "    default: wire c;\n"
      "  endcase\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kGenerateCase));
}

TEST(CheckerItemsParsing, CheckerGenerateRegion) {
  auto r = Parse(
      "checker my_chk;\n"
      "  generate\n"
      "    wire w;\n"
      "  endgenerate\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CheckerItemsParsing, CheckerElabTaskErrorSeverity) {
  auto r = Parse(
      "checker chk;\n"
      "  $error(\"something wrong\");\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kElabSystemTask));
}

TEST(CheckerItemsParsing, CheckerMultipleItemTypes) {
  auto r = Parse(
      "checker chk(input logic clk, output bit ok);\n"
      "  logic sig;\n"
      "  assign ok = sig;\n"
      "  initial begin end\n"
      "  always @(posedge clk) sig <= 1;\n"
      "  final begin end\n"
      "  assert property (@(posedge clk) sig);\n"
      "  default disable iff !ok;\n"
      "  function int f(); return 0; endfunction\n"
      "  $warning(\"test\");\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  auto* chk = r.cu->checkers[0];
  EXPECT_EQ(chk->name, "chk");
  ASSERT_EQ(chk->ports.size(), 2u);
  EXPECT_TRUE(HasItemKind(chk->items, ModuleItemKind::kVarDecl));
  EXPECT_TRUE(HasItemKind(chk->items, ModuleItemKind::kContAssign));
  EXPECT_TRUE(HasItemKind(chk->items, ModuleItemKind::kInitialBlock));
  EXPECT_TRUE(HasItemKind(chk->items, ModuleItemKind::kAlwaysBlock));
  EXPECT_TRUE(HasItemKind(chk->items, ModuleItemKind::kFinalBlock));
  EXPECT_TRUE(HasItemKind(chk->items, ModuleItemKind::kAssertProperty));
  EXPECT_TRUE(HasItemKind(chk->items, ModuleItemKind::kDefaultDisableIff));
  EXPECT_TRUE(HasItemKind(chk->items, ModuleItemKind::kFunctionDecl));
  EXPECT_TRUE(HasItemKind(chk->items, ModuleItemKind::kElabSystemTask));
}

TEST(CheckerItemsParsing, CheckerPortListInheritedDirection) {
  auto r = Parse(
      "checker chk(input logic a, b);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_EQ(r.cu->checkers[0]->ports.size(), 2u);
  EXPECT_EQ(r.cu->checkers[0]->ports[0].name, "a");
  EXPECT_EQ(r.cu->checkers[0]->ports[0].direction, Direction::kInput);
  EXPECT_EQ(r.cu->checkers[0]->ports[1].name, "b");
  EXPECT_EQ(r.cu->checkers[0]->ports[1].direction, Direction::kInput);
}

TEST(CheckerItemsParsing, CheckerPortMissingIdentifierRejected) {
  auto r = Parse(
      "checker chk(input logic);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got ')'", 1, "23.2.2.2"));
}

TEST(CheckerItemsParsing, CheckerDefaultDisableIffMissingSemicolonRejected) {
  auto r = Parse(
      "checker chk;\n"
      "  default disable iff rst\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endchecker'", 3, "16.15"));
}

TEST(CheckerItemsParsing, CheckerSpecifyBlockRejected) {
  auto r = Parse(
      "checker c;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "  endspecify\n"
      "  initial x = 0;\n"
      "endchecker\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "specify block must appear inside a module declaration", 2,
      "30.3"));
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kInitialBlock));
}

TEST(CheckerItemsParsing, CheckerSpecparamRejected) {
  auto r = Parse(
      "checker c;\n"
      "  specparam tRise = 150;\n"
      "endchecker\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "specparam declaration must appear inside a module or a specify block", 2,
      "6.20.5"));
}

TEST(CheckerItemsParsing, CheckerPortListOfComplexCheckerExample) {
  auto r = Parse(
      "typedef enum { cover_none, cover_all } coverage_level;\n"
      "checker assert_window1 (\n"
      "  logic test_expr,\n"
      "  untyped start_event,\n"
      "  untyped end_event,\n"
      "  event clock = $inferred_clock,\n"
      "  logic reset = $inferred_disable,\n"
      "  string error_msg = \"violation\",\n"
      "  coverage_level clevel = cover_all\n"
      ");\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  const auto& ports = r.cu->checkers[0]->ports;
  ASSERT_EQ(ports.size(), 7u);
  EXPECT_EQ(ports[0].formal_type, PropertyFormalType::kData);
  EXPECT_EQ(ports[0].data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(ports[1].name, "start_event");
  EXPECT_EQ(ports[1].formal_type, PropertyFormalType::kUntyped);
  EXPECT_EQ(ports[1].direction, Direction::kInput);
  EXPECT_EQ(ports[2].formal_type, PropertyFormalType::kUntyped);
  EXPECT_EQ(ports[3].data_type.kind, DataTypeKind::kEvent);
  EXPECT_NE(ports[3].default_value, nullptr);
  EXPECT_EQ(ports[6].name, "clevel");
  EXPECT_EQ(ports[6].data_type.kind, DataTypeKind::kNamed);
  EXPECT_NE(ports[6].default_value, nullptr);
}

TEST(CheckerItemsParsing, CheckerPortSequenceAndPropertyFormals) {
  auto r = Parse(
      "checker chk(sequence s, property p, untyped u, input logic x);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  const auto& ports = r.cu->checkers[0]->ports;
  ASSERT_EQ(ports.size(), 4u);
  EXPECT_EQ(ports[0].formal_type, PropertyFormalType::kSequence);
  EXPECT_EQ(ports[0].direction, Direction::kInput);
  EXPECT_EQ(ports[1].formal_type, PropertyFormalType::kProperty);
  EXPECT_EQ(ports[1].direction, Direction::kInput);
  EXPECT_EQ(ports[2].formal_type, PropertyFormalType::kUntyped);
  EXPECT_EQ(ports[3].formal_type, PropertyFormalType::kData);
  EXPECT_EQ(ports[3].data_type.kind, DataTypeKind::kLogic);
}

TEST(CheckerItemsParsing, CheckerPortKeywordTypeInheritedByBareFormal) {
  auto r = Parse(
      "checker chk(sequence s, t);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_EQ(r.cu->checkers[0]->ports.size(), 2u);
  EXPECT_EQ(r.cu->checkers[0]->ports[1].name, "t");
  EXPECT_EQ(r.cu->checkers[0]->ports[1].formal_type,
            PropertyFormalType::kSequence);
}

TEST(CheckerItemsParsing, CheckerPortListIsNotANonAnsiList) {
  auto r = Parse(
      "checker chk(a, logic b);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_FALSE(r.cu->checkers[0]->is_non_ansi_ports);
  ASSERT_EQ(r.cu->checkers[0]->ports.size(), 2u);
  EXPECT_EQ(r.cu->checkers[0]->ports[0].name, "a");
  EXPECT_EQ(r.cu->checkers[0]->ports[0].formal_type,
            PropertyFormalType::kUntyped);
  EXPECT_EQ(r.cu->checkers[0]->ports[1].name, "b");
  EXPECT_EQ(r.cu->checkers[0]->ports[1].data_type.kind, DataTypeKind::kLogic);
}

TEST(CheckerItemsParsing, CheckerPortExplicitNamedFormRejected) {
  auto r = Parse(
      "checker chk(.a(x));\n"
      "endchecker\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "checker formal 'a' is named by an identifier "
                            "alone",
                            1, "A.1.8"));
}

TEST(CheckerItemsParsing, CheckerTaskDeclarationRejected) {
  auto r = Parse(
      "checker c;\n"
      "  task t();\n"
      "  endtask\n"
      "  initial x = 0;\n"
      "endchecker\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a task declaration is not an item of a checker", 2, "A.1.8"));
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kInitialBlock));
}

TEST(CheckerItemsParsing, CheckerClassDeclarationRejected) {
  auto r = Parse(
      "checker c;\n"
      "  class k;\n"
      "  endclass\n"
      "endchecker\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a class declaration is not an item of a checker", 2, "A.1.8"));
}

TEST(CheckerItemsParsing, CheckerExternalConstraintBlockRejected) {
  auto r = Parse(
      "checker c;\n"
      "  constraint k::p { 1; }\n"
      "endchecker\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "an external constraint block is not an item of a checker", 2,
      "A.1.8"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.cu->external_constraints.empty());
}

TEST(CheckerItemsParsing, CheckerParameterDeclarationRejected) {
  auto r = Parse(
      "checker c;\n"
      "  localparam int W = 4;\n"
      "  parameter int D = 2;\n"
      "endchecker\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a parameter declaration is not an item of a "
                            "checker",
                            2, "A.1.8"));
  EXPECT_TRUE(ReportedError(r.diags,
                            "a parameter declaration is not an item of a "
                            "checker",
                            3, "A.1.8"));
}

TEST(CheckerItemsParsing, CheckerDefparamRejected) {
  auto r = Parse(
      "checker c;\n"
      "  defparam u.p = 1;\n"
      "endchecker\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a defparam statement is not an item of a checker", 2, "A.1.8"));
}

TEST(CheckerItemsParsing, CheckerNetAliasRejected) {
  auto r = Parse(
      "checker c;\n"
      "  alias a = b;\n"
      "endchecker\n");
  EXPECT_TRUE(ReportedError(r.diags, "a net alias is not an item of a checker",
                            2, "A.1.8"));
}

TEST(CheckerItemsParsing, CheckerBindDirectiveRejected) {
  auto r = Parse(
      "checker c;\n"
      "  bind m chk u();\n"
      "endchecker\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a bind directive is not an item of a checker", 2, "A.1.8"));
}

TEST(CheckerItemsParsing, CheckerTimeunitRejected) {
  auto r = Parse(
      "checker c;\n"
      "  timeunit 1ns;\n"
      "endchecker\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a timeunit or timeprecision declaration is not "
                            "an item of a checker",
                            2, "A.1.8"));
}

TEST(CheckerItemsParsing, CheckerGateInstantiationRejected) {
  auto r = Parse(
      "checker c;\n"
      "  and g(o, a, b);\n"
      "endchecker\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a gate instantiation is not an item of a checker", 2, "A.1.8"));
}

TEST(CheckerItemsParsing, CheckerBodyPortDeclarationRejected) {
  auto r = Parse(
      "checker c;\n"
      "  input clk;\n"
      "  initial x = 0;\n"
      "endchecker\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a port declaration is not an item of a checker", 2, "A.1.8"));
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kInitialBlock));
}

TEST(CheckerItemsParsing, CheckerPackageDeclarationRejected) {
  auto r = Parse(
      "checker c;\n"
      "  package p;\n"
      "    int q;\n"
      "  endpackage\n"
      "  initial x = 0;\n"
      "endchecker\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a package cannot be declared inside checker 'c'", 2, "17.2"));
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_FALSE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kVarDecl));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kInitialBlock));
}

TEST(CheckerItemsParsing, CheckerGenerateBlockAdmitsCheckerItemsOnly) {
  auto r = Parse(
      "checker c;\n"
      "  if (1) begin : g\n"
      "    task t();\n"
      "    endtask\n"
      "  end\n"
      "endchecker\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a task declaration is not an item of a checker", 3, "A.1.8"));
}

TEST(CheckerItemsParsing, CheckerDpiImportAndExportRejected) {
  auto r = Parse(
      "checker c;\n"
      "  import \"DPI-C\" function int f();\n"
      "  function int g(); return 0; endfunction\n"
      "  export \"DPI-C\" function g;\n"
      "endchecker\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a DPI import declaration is not an item of a "
                            "checker",
                            2, "A.1.8"));
  EXPECT_TRUE(ReportedError(r.diags,
                            "a DPI export declaration is not an item of a "
                            "checker",
                            4, "A.1.8"));
  EXPECT_FALSE(
      ReportedError(r.diags, "is not an item of a checker", 3, "A.1.8"));
}

TEST(CheckerItemsParsing, CheckerFormalDefaultIsAnActualArgument) {
  auto r = Parse(
      "checker c(logic a, logic b, sequence s = a ##1 b,\n"
      "          event e = posedge a, event clk = $inferred_clock,\n"
      "          int n = 3);\n"
      "  cover property (@e s);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  const auto& ports = r.cu->checkers[0]->ports;
  ASSERT_EQ(ports.size(), 6u);
  for (size_t i = 2; i < ports.size(); ++i) {
    EXPECT_NE(ports[i].default_value, nullptr) << ports[i].name;
  }
}

TEST(CheckerItemsParsing, InheritedTypeFormalDefaultIsAnActualArgument) {
  auto r = Parse(
      "checker c(logic a, logic b, sequence s1 = a ##1 b, s2 = b ##2 a);\n"
      "endchecker\n"
      "module m(input int x = 1, y = 2);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_EQ(r.cu->checkers[0]->ports.size(), 4u);
  EXPECT_NE(r.cu->checkers[0]->ports[3].default_value, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
  EXPECT_NE(r.cu->modules[0]->ports[1].default_value, nullptr);
}

TEST(CheckerItemsParsing, CheckerGenerateBlockDpiImportRejected) {
  auto r = Parse(
      "checker c;\n"
      "  if (1) begin : g\n"
      "    import \"DPI-C\" function void f();\n"
      "  end\n"
      "endchecker\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a DPI import declaration is not an item of a "
                            "checker",
                            3, "A.1.8"));
}

TEST(CheckerItemsParsing,
     ModuleDpiDeclarationsAndCheckerPackageImportAccepted) {
  auto r = Parse(
      "package p; int v; endpackage\n"
      "module m;\n"
      "  import \"DPI-C\" function int f();\n"
      "  function int g(); return 0; endfunction\n"
      "  export \"DPI-C\" function g;\n"
      "endmodule\n"
      "checker c;\n"
      "  import p::*;\n"
      "endchecker\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(CheckerItemsParsing, RandOutsideACheckerIsReported) {
  auto r = Parse(
      "module m;\n"
      "  rand bit b;\n"
      "endmodule\n"
      "interface i;\n"
      "  rand logic v;\n"
      "endinterface\n"
      "program p;\n"
      "  rand int n;\n"
      "endprogram\n"
      "package k;\n"
      "  rand bit q;\n"
      "endpackage\n"
      "checker c;\n"
      "  rand bit r;\n"
      "  if (1) begin : g\n"
      "    rand bit s;\n"
      "  end\n"
      "endchecker\n");
  const char* const kRand = "only a checker's data declaration opens with rand";
  EXPECT_TRUE(ReportedError(r.diags, kRand, 2, "A.1.8"));
  EXPECT_TRUE(ReportedError(r.diags, kRand, 5, "A.1.8"));
  EXPECT_TRUE(ReportedError(r.diags, kRand, 8, "A.1.8"));
  EXPECT_TRUE(ReportedError(r.diags, kRand, 11, "A.1.8"));
  EXPECT_FALSE(ReportedError(r.diags, kRand, 14, "A.1.8"));
  EXPECT_FALSE(ReportedError(r.diags, kRand, 16, "A.1.8"));
}

}  // namespace

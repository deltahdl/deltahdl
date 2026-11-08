#include <gtest/gtest.h>

#include <iterator>
#include <string>

#include "fixture_parser.h"
#include "helpers_keyword_version.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "model_keyword_tables.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

constexpr const char* kExcluded[] = {
    "cell",    "config",   "design",  "endconfig", "incdir",
    "include", "instance", "liblist", "library",   "use",
};

constexpr const char* kKept[] = {
    "automatic",
    "endgenerate",
    "generate",
    "genvar",
    "localparam",
    "noshowcancelled",
    "pulsestyle_ondetect",
    "pulsestyle_onevent",
    "showcancelled",
    "signed",
    "unsigned",
};

bool ParsesNoconfig(const std::string& body) {
  return ParseWithPreprocessorOk(InNoconfig(body));
}
TEST(CompilerDirectiveParsing, NoconfigExcludedWordsCanNameAVariable) {
  EXPECT_EQ(std::size(kExcluded), 10u);
  for (const char* word : kExcluded) {
    EXPECT_TRUE(ParseWithPreprocessorOk(InNoconfig(VarDecl(word))))
        << word << " is dropped from the reserved list by this version";
    auto r = ParseWithPreprocessor(In2001(VarDecl(word)));
    EXPECT_TRUE(ReportedError(
        r.diags, std::string("expected identifier, got '") + word + "'",
        LineInRegion(2), "6.8"))
        << word << " is reserved by the version this one is defined from";
  }
}

TEST(CompilerDirectiveParsing, NoconfigKeepsOtherVerilog2001AdditionsReserved) {
  EXPECT_EQ(std::size(kKept), 11u);
  for (const char* word : kKept) {
    auto r = ParseWithPreprocessor(InNoconfig(VarDecl(word)));
    EXPECT_TRUE(ReportedError(
        r.diags, std::string("expected identifier, got '") + word + "'",
        LineInRegion(2), "6.8"))
        << word << " is not among the ten this version drops";
    EXPECT_TRUE(ParseWithPreprocessorOk(In1995(VarDecl(word))))
        << word << " is an addition of 1364-2001, not of the list it extends";
  }
}

TEST(CompilerDirectiveParsing, NoconfigKeepsAllVerilog1995KeywordsReserved) {
  EXPECT_EQ(std::size(kVerilog1995Keywords), 102u);
  for (const char* word : kVerilog1995Keywords) {
    auto r = ParseWithPreprocessor(InNoconfig(VarDecl(word)));
    EXPECT_TRUE(ReportedError(
        r.diags, std::string("expected identifier, got '") + word + "'",
        LineInRegion(2), "6.8"))
        << word << " is inherited from Table 22-1 and stays reserved";
  }
}

TEST(CompilerDirectiveParsing, NoconfigExcludedWordsNameEveryDeclaredEntity) {
  auto r = ParseWithPreprocessor(
      InNoconfig("module cell (input wire design, output wire library);\n"
                 "  parameter incdir = 4;\n"
                 "  wire [7:0] instance;\n"
                 "  reg  [7:0] liblist;\n"
                 "  reg  [7:0] endconfig;\n"
                 "  task use; begin liblist = 8'd9; end endtask\n"
                 "  initial begin : include\n"
                 "    use;\n"
                 "  end\n"
                 "  assign library = design;\n"
                 "endmodule\n"
                 "module top;\n"
                 "  wire a, b;\n"
                 "  cell config (.design(a), .library(b));\n"
                 "endmodule\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);

  auto* m = r.cu->modules[0];
  EXPECT_EQ(m->name, "cell");
  ASSERT_EQ(m->ports.size(), 2u);
  EXPECT_EQ(m->ports[0].name, "design");
  EXPECT_EQ(m->ports[1].name, "library");
  EXPECT_TRUE(HasItemKindNamed(m->items, ModuleItemKind::kParamDecl, "incdir"));
  EXPECT_TRUE(HasItemKindNamed(m->items, ModuleItemKind::kNetDecl, "instance"));
  EXPECT_TRUE(HasItemKindNamed(m->items, ModuleItemKind::kVarDecl, "liblist"));
  EXPECT_TRUE(
      HasItemKindNamed(m->items, ModuleItemKind::kVarDecl, "endconfig"));
  EXPECT_TRUE(HasItemKindNamed(m->items, ModuleItemKind::kTaskDecl, "use"));

  auto* u =
      FindItemByKind(r.cu->modules[1]->items, ModuleItemKind::kModuleInst);
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(u->inst_module, "cell");
  EXPECT_EQ(u->inst_name, "config");
}

TEST(CompilerDirectiveParsing, NoconfigExcludedWordIsOperandAndAssignTarget) {
  auto r =
      ParseWithPreprocessor(InNoconfig("module m;\n"
                                       "  reg [7:0] library;\n"
                                       "  reg [7:0] result;\n"
                                       "  initial begin\n"
                                       "    library = 8'd5;\n"
                                       "    result = library + 8'd1;\n"
                                       "  end\n"
                                       "endmodule\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto* first = NthInitialStmt(r, 0);
  ASSERT_NE(first, nullptr);
  ASSERT_NE(first->lhs, nullptr);
  EXPECT_EQ(first->lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(first->lhs->text, "library");

  auto* second = NthInitialStmt(r, 1);
  ASSERT_NE(second, nullptr);
  ASSERT_NE(second->rhs, nullptr);
  EXPECT_EQ(second->rhs->kind, ExprKind::kBinary);
  ASSERT_NE(second->rhs->lhs, nullptr);
  EXPECT_EQ(second->rhs->lhs->text, "library");
}

TEST(CompilerDirectiveParsing, NoconfigExcludedWordNamesOtherDeclarationKinds) {
  auto r = ParseWithPreprocessor(
      InNoconfig("module m (input wire a, output wire y);\n"
                 "  event design;\n"
                 "  reg   result;\n"
                 "  and   instance (y, a, a);\n"
                 "  function include;\n"
                 "    input x;\n"
                 "    include = ~x;\n"
                 "  endfunction\n"
                 "  initial begin\n"
                 "    -> design;\n"
                 "    result = include(1'b0);\n"
                 "  end\n"
                 "endmodule\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto& items = r.cu->modules[0]->items;
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kVarDecl, "design"));
  EXPECT_TRUE(
      HasItemKindNamed(items, ModuleItemKind::kFunctionDecl, "include"));

  auto* gate = FindGateByKind(items, GateKind::kAnd);
  ASSERT_NE(gate, nullptr);
  EXPECT_EQ(gate->gate_inst_name, "instance");
}

TEST(CompilerDirectiveParsing, NoconfigExcludedWordNamesASubroutineArgument) {
  auto r = ParseWithPreprocessor(
      InNoconfig("module m;\n"
                 "  reg [7:0] result;\n"
                 "  function [7:0] twice(input reg [7:0] library);\n"
                 "    twice = library + library;\n"
                 "  endfunction\n"
                 "  task bump(input reg [7:0] incdir);\n"
                 "    result = result + incdir;\n"
                 "  endtask\n"
                 "  initial begin\n"
                 "    result = 8'd0;\n"
                 "    bump(twice(8'd4));\n"
                 "  end\n"
                 "endmodule\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto& items = r.cu->modules[0]->items;
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kFunctionDecl, "twice"));
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kTaskDecl, "bump"));

  auto as_func_arg = ParseWithPreprocessor(
      In2001("module m;\n"
             "  function [7:0] twice(input reg [7:0] library);\n"
             "    twice = library;\n"
             "  endfunction\n"
             "endmodule\n"));
  EXPECT_TRUE(ReportedError(as_func_arg.diags,
                            "tf_port_item shall include a port_identifier",
                            LineInRegion(2), "13.3"));

  auto as_task_arg =
      ParseWithPreprocessor(In2001("module m;\n"
                                   "  reg [7:0] result;\n"
                                   "  task bump(input reg [7:0] incdir);\n"
                                   "    result = incdir;\n"
                                   "  endtask\n"
                                   "endmodule\n"));
  EXPECT_TRUE(ReportedError(as_task_arg.diags,
                            "tf_port_item shall include a port_identifier",
                            LineInRegion(3), "13.3"));
}

TEST(CompilerDirectiveParsing, NoconfigCannotWriteAConfigDeclaration) {
  const std::string kSrc =
      "module top;\n"
      "endmodule\n"
      "config config_a;\n"
      "  design lib.top;\n"
      "  default liblist blue green;\n"
      "  instance top.u1 liblist red;\n"
      "  cell m1 use lib.m2;\n"
      "endconfig\n";

  auto under_2001 = ParseWithPreprocessor(In2001(kSrc));
  ASSERT_NE(under_2001.cu, nullptr);
  EXPECT_FALSE(under_2001.has_errors);
  ASSERT_EQ(under_2001.cu->configs.size(), 1u);
  auto* cfg = under_2001.cu->configs[0];
  EXPECT_EQ(cfg->name, "config_a");
  EXPECT_EQ(cfg->design_cells.size(), 1u);
  EXPECT_EQ(cfg->rules.size(), 3u);

  auto dropped = ParseWithPreprocessor(InNoconfig(kSrc));
  EXPECT_TRUE(ReportedError(dropped.diags, "expected top-level declaration",
                            LineInRegion(3), "3.12.1"));

  EXPECT_TRUE(ParsesNoconfig("module top;\nendmodule\n"));
}

TEST(CompilerDirectiveParsing, NoconfigFreesTheWordThatOpensAConfiguration) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk(In2001("config c;\n"
                                     "  design lib.top;\n"
                                     "endconfig\n")));
  auto dropped =
      ParseWithPreprocessor(InNoconfig("config c;\n"
                                       "  design lib.top;\n"
                                       "endconfig\n"));
  EXPECT_TRUE(ReportedError(dropped.diags, "expected top-level declaration",
                            LineInRegion(1), "3.12.1"));

  auto r = ParseWithPreprocessor(InNoconfig("module config;\nendmodule\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "config");
  EXPECT_TRUE(r.cu->configs.empty());
}

TEST(CompilerDirectiveParsing, NoconfigKeptAdditionsStillOpenTheirConstructs) {
  auto r = ParseWithPreprocessor(
      InNoconfig("module m;\n"
                 "  parameter  P = 8;\n"
                 "  localparam L = 8;\n"
                 "  genvar g;\n"
                 "  reg  unsigned [7:0] u;\n"
                 "  wire signed   [7:0] sw;\n"
                 "  function automatic integer widthof(input reg [7:0] n);\n"
                 "    widthof = n;\n"
                 "  endfunction\n"
                 "  task automatic bump(input reg [7:0] d);\n"
                 "    u = u + d;\n"
                 "  endtask\n"
                 "  reg [L-1:0]          from_localparam;\n"
                 "  reg [widthof(8)-1:0] from_function;\n"
                 "  generate\n"
                 "    for (g = 0; g < 2; g = g + 1) begin : blk\n"
                 "      reg [g+8-1:0] e;\n"
                 "    end\n"
                 "  endgenerate\n"
                 "endmodule\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto& items = r.cu->modules[0]->items;
  auto* l = FindItemByName(items, "L");
  ASSERT_NE(l, nullptr);
  EXPECT_EQ(l->kind, ModuleItemKind::kParamDecl);
  EXPECT_TRUE(l->is_localparam);

  EXPECT_NE(FindItemByKind(items, ModuleItemKind::kGenerateFor), nullptr);
  EXPECT_TRUE(
      HasItemKindNamed(items, ModuleItemKind::kFunctionDecl, "widthof"));
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kTaskDecl, "bump"));
}

TEST(CompilerDirectiveParsing, NoconfigKeepsPulseControlKeywords) {
  auto r = ParseWithPreprocessor(
      InNoconfig("module m (input wire a, output wire y);\n"
                 "  assign y = a;\n"
                 "  specify\n"
                 "    showcancelled y;\n"
                 "    noshowcancelled y;\n"
                 "    pulsestyle_ondetect y;\n"
                 "    pulsestyle_onevent y;\n"
                 "    (a => y) = 1;\n"
                 "  endspecify\n"
                 "endmodule\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_NE(FindSpecifyBlock(r.cu->modules[0]->items), nullptr);
}

TEST(CompilerDirectiveParsing, NoconfigExcludedWordNamesAModule) {
  EXPECT_TRUE(ParsesNoconfig("module config;\nendmodule\n"));
  auto as_module = ParseWithPreprocessor(In2001("module config;\nendmodule\n"));
  EXPECT_TRUE(ReportedError(as_module.diags,
                            "expected identifier, got 'config'",
                            LineInRegion(1), "23.2.1"));

  EXPECT_TRUE(
      ParsesNoconfig("module sub;\nendmodule\n"
                     "module top;\n  sub library ();\nendmodule\n"));
  auto as_instance =
      ParseWithPreprocessor(In2001("module sub;\nendmodule\n"
                                   "module top;\n  sub library ();\n"
                                   "endmodule\n"));
  EXPECT_TRUE(ReportedError(as_instance.diags, "expected ';', got 'library'",
                            LineInRegion(4), "6.8"));
}

TEST(CompilerDirectiveParsing, NoconfigKeptAdditionCannotNameAModule) {
  auto as_module =
      ParseWithPreprocessor(InNoconfig("module generate;\n"
                                       "endmodule\n"));
  EXPECT_TRUE(ReportedError(as_module.diags,
                            "expected identifier, got 'generate'",
                            LineInRegion(1), "23.2.1"));
  EXPECT_TRUE(ParseWithPreprocessorOk(In1995("module generate;\nendmodule\n")));

  auto as_instance =
      ParseWithPreprocessor(InNoconfig("module sub;\nendmodule\n"
                                       "module top;\n  sub localparam ();\n"
                                       "endmodule\n"));
  EXPECT_TRUE(ReportedError(as_instance.diags, "expected ';', got 'localparam'",
                            LineInRegion(4), "6.8"));
}

TEST(CompilerDirectiveParsing, WordOutsideNoconfigListIsNotAKeyword) {
  auto as_net =
      ParseWithPreprocessor(InNoconfig("module m;\n  uwire w;\n"
                                       "endmodule\n"));
  ASSERT_NE(as_net.cu, nullptr);
  auto* as_net_item = as_net.cu->modules[0]->items[0];
  EXPECT_EQ(as_net_item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(as_net_item->data_type.type_name, "uwire");
  EXPECT_TRUE(as_net_item->type_name_undeclared_at_parse);
  EXPECT_TRUE(ParseWithPreprocessorOk("module m;\n  uwire w;\nendmodule\n"));

  auto as_type =
      ParseWithPreprocessor(InNoconfig("module m;\n"
                                       "  logic [7:0] v;\n"
                                       "endmodule\n"));
  EXPECT_TRUE(ReportedError(as_type.diags, "expected ';', got '['",
                            LineInRegion(2), "6.8"));
  EXPECT_TRUE(
      ParseWithPreprocessorOk("module m;\n  logic [7:0] v;\nendmodule\n"));

  auto as_decl =
      ParseWithPreprocessor(InNoconfig("module m;\n"
                                       "  reg r;\n"
                                       "  always_comb r = 1'b0;\n"
                                       "endmodule\n"));
  ASSERT_NE(as_decl.cu, nullptr);
  EXPECT_FALSE(as_decl.has_errors);
  ASSERT_EQ(as_decl.cu->modules.size(), 1u);
  auto& decl_items = as_decl.cu->modules[0]->items;
  ASSERT_EQ(decl_items.size(), 2u);
  EXPECT_EQ(decl_items[1]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(decl_items[1]->name, "r");
  EXPECT_EQ(decl_items[1]->data_type.type_name, "always_comb");
  EXPECT_TRUE(decl_items[1]->type_name_undeclared_at_parse);
  ASSERT_NE(decl_items[1]->init_expr, nullptr);
  EXPECT_EQ(decl_items[1]->init_expr->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(decl_items[1]->init_expr->text, "1'b0");

  auto outside = ParseWithPreprocessor(
      "module m;\n"
      "  reg r;\n"
      "  always_comb r = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(outside.cu, nullptr);
  EXPECT_FALSE(outside.has_errors);
  ASSERT_EQ(outside.cu->modules.size(), 1u);
  auto& outside_items = outside.cu->modules[0]->items;
  ASSERT_EQ(outside_items.size(), 2u);
  EXPECT_EQ(outside_items[1]->kind, ModuleItemKind::kAlwaysCombBlock);
}

TEST(CompilerDirectiveParsing, NoconfigLeavesUnlistedWordsFree) {
  auto r = ParseWithPreprocessor(
      InNoconfig("module bit (input wire logic, output wire byte);\n"
                 "  parameter int = 4;\n"
                 "  reg [7:0] longint;\n"
                 "  assign byte = logic;\n"
                 "endmodule\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto* m = r.cu->modules[0];
  EXPECT_EQ(m->name, "bit");
  ASSERT_EQ(m->ports.size(), 2u);
  EXPECT_EQ(m->ports[0].name, "logic");
  EXPECT_EQ(m->ports[1].name, "byte");
  EXPECT_TRUE(HasItemKindNamed(m->items, ModuleItemKind::kParamDecl, "int"));
  EXPECT_TRUE(HasItemKindNamed(m->items, ModuleItemKind::kVarDecl, "longint"));
}

}  // namespace

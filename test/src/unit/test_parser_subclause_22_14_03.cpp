#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "helpers_included_keyword_parse.h"
#include "helpers_keyword_version.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "model_keyword_tables.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

bool Parses2001(const std::string& body) {
  return ParseWithPreprocessorOk(In2001(body));
}

TEST(CompilerDirectiveParsing, Verilog2001AdditionsCannotNameAVariable) {
  for (const char* word : kVerilog2001AddedKeywords) {
    std::string decl =
        std::string("module m;\n  reg [7:0] ") + word + ";\nendmodule\n";
    auto r = ParseWithPreprocessor(In2001(decl));
    EXPECT_TRUE(ReportedError(
        r.diags, std::string("expected identifier, got '") + word + "'",
        LineInRegion(2), "6.8"))
        << word << " is reserved by Table 22-2";
    EXPECT_TRUE(ParseWithPreprocessorOk(In1995(decl)))
        << word << " is not in the list this version extends";
  }
}

TEST(CompilerDirectiveParsing, InheritedKeywordsCannotNameAVariable) {
  EXPECT_EQ(std::size(kVerilog1995Keywords), 102u);
  for (const char* word : kVerilog1995Keywords) {
    std::string decl =
        std::string("module m;\n  reg [7:0] ") + word + ";\nendmodule\n";
    auto r = ParseWithPreprocessor(In2001(decl));
    EXPECT_TRUE(ReportedError(
        r.diags, std::string("expected identifier, got '") + word + "'",
        LineInRegion(2), "6.8"))
        << word << " is carried over from Table 22-1 and stays reserved";
  }
}

TEST(CompilerDirectiveParsing, Verilog2001ConstantKeywordsDeclareConstants) {
  auto r = ParseWithPreprocessor(
      In2001("module m;\n"
             "  parameter  P = 8;\n"
             "  localparam L = 8;\n"
             "  genvar g;\n"
             "  function automatic integer widthof(input reg [7:0] n);\n"
             "    widthof = n;\n"
             "  endfunction\n"
             "  reg [7:0]            a;\n"
             "  reg [P-1:0]          b;\n"
             "  reg [L-1:0]          c;\n"
             "  reg [widthof(8)-1:0] d;\n"
             "  generate\n"
             "    for (g = 0; g < 2; g = g + 1) begin : blk\n"
             "      reg [g+8-1:0] e;\n"
             "    end\n"
             "  endgenerate\n"
             "endmodule\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto& items = r.cu->modules[0]->items;
  auto* p = FindItemByName(items, "P");
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->kind, ModuleItemKind::kParamDecl);
  EXPECT_FALSE(p->is_localparam);

  auto* l = FindItemByName(items, "L");
  ASSERT_NE(l, nullptr);
  EXPECT_EQ(l->kind, ModuleItemKind::kParamDecl);
  EXPECT_TRUE(l->is_localparam);

  EXPECT_NE(FindItemByKind(items, ModuleItemKind::kGenerateFor), nullptr);
  EXPECT_TRUE(
      HasItemKindNamed(items, ModuleItemKind::kFunctionDecl, "widthof"));
}

TEST(CompilerDirectiveParsing, SignedAndUnsignedQualifyDeclarations) {
  auto r = ParseWithPreprocessor(
      In2001("module m (input wire signed [7:0] a,\n"
             "          output wire signed [7:0] y);\n"
             "  parameter signed [7:0] P = -8'sd3;\n"
             "  reg  unsigned [7:0] u;\n"
             "  wire signed   [7:0] sw;\n"
             "  assign sw = a;\n"
             "  assign y  = sw;\n"
             "  function signed [7:0] neg(input reg signed [7:0] x);\n"
             "    neg = -x;\n"
             "  endfunction\n"
             "endmodule\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemKindNamed(r.cu->modules[0]->items,
                               ModuleItemKind::kFunctionDecl, "neg"));
}

TEST(CompilerDirectiveParsing, AutomaticQualifiesTasksAndFunctions) {
  auto r =
      ParseWithPreprocessor(In2001("module m;\n"
                                   "  reg [7:0] r;\n"
                                   "  task automatic bump(input reg [7:0] d);\n"
                                   "    r = r + d;\n"
                                   "  endtask\n"
                                   "  function automatic [7:0] twice;\n"
                                   "    input x;\n"
                                   "    twice = x ? 8'd2 : 8'd0;\n"
                                   "  endfunction\n"
                                   "endmodule\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto& items = r.cu->modules[0]->items;
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kTaskDecl, "bump"));
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kFunctionDecl, "twice"));
}

TEST(CompilerDirectiveParsing, PulseControlKeywordsOpenSpecifyItems) {
  auto r =
      ParseWithPreprocessor(In2001("module m (input wire a, output wire y);\n"
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

TEST(CompilerDirectiveParsing, Verilog1995KeywordRolesSurviveUnder2001) {
  auto r = ParseWithPreprocessor(
      In2001("module m;\n"
             "  reg a, b, e;\n"
             "  wire y, z, w, p;\n"
             "  wand  n1;\n"
             "  trior n2;\n"
             "  trireg (large) n3;\n"
             "  supply1 n4;\n"
             "  and    g1 (y, a, b);\n"
             "  nor    g2 (z, a, b);\n"
             "  buf    (strong1, weak0) g3 (w, a);\n"
             "  bufif0 g4 (p, a, e);\n"
             "  cmos   s1 (w, a, b, e);\n"
             "  tranif1 s2 (y, z, e);\n"
             "  integer i;\n"
             "  event ev;\n"
             "  initial begin : blk\n"
             "    for (i = 0; i < 2; i = i + 1) a = 1'b0;\n"
             "    repeat (2) b = 1'b1;\n"
             "    casez (a)\n"
             "      1'b0: b = 1'b1;\n"
             "      default: b = 1'b0;\n"
             "    endcase\n"
             "    fork a = 1'b1; join\n"
             "    -> ev;\n"
             "    force a = 1'b1;\n"
             "    release a;\n"
             "    disable blk;\n"
             "  end\n"
             "  always @(posedge a or negedge b)\n"
             "    if (b) i <= i + 1;\n"
             "    else i <= 0;\n"
             "endmodule\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto& items = r.cu->modules[0]->items;
  const GateKind kExpected[] = {GateKind::kAnd,  GateKind::kNor,
                                GateKind::kBuf,  GateKind::kBufif0,
                                GateKind::kCmos, GateKind::kTranif1};
  for (auto kind : kExpected) {
    EXPECT_NE(FindGateByKind(items, kind), nullptr)
        << "gate kind " << static_cast<int>(kind);
  }

  auto* always_item = FirstAlwaysItem(r);
  ASSERT_NE(always_item, nullptr);
  ASSERT_EQ(always_item->sensitivity.size(), 2u);
  EXPECT_EQ(always_item->sensitivity[0].edge, Edge::kPosedge);
  EXPECT_EQ(always_item->sensitivity[1].edge, Edge::kNegedge);
}

TEST(CompilerDirectiveParsing, InheritedSpecifyAndPrimitiveKeywordsParse) {
  EXPECT_TRUE(
      Parses2001("macromodule m (input wire a, output wire y);\n"
                 "  assign y = a;\n"
                 "  specify\n"
                 "    specparam tr = 1;\n"
                 "    (a => y) = tr;\n"
                 "  endspecify\n"
                 "endmodule\n"));
  EXPECT_TRUE(
      Parses2001("primitive p (out, in);\n"
                 "  output out;\n"
                 "  input in;\n"
                 "  table\n"
                 "    0 : 1;\n"
                 "    1 : 0;\n"
                 "  endtable\n"
                 "endprimitive\n"));
}

TEST(CompilerDirectiveParsing, Verilog2001FreedWordNamesDeclaredEntities) {
  ExpectFreedWordsNameDeclaredEntities("1364-2001");
}

TEST(CompilerDirectiveParsing,
     Verilog2001FreedWordIsAnOperandAndAssignmentTarget) {
  ExpectFreedWordIsAnOperandAndAssignmentTarget("1364-2001");
}

TEST(CompilerDirectiveParsing,
     Verilog2001FreedWordNamesEveryOtherDeclarationKind) {
  auto r =
      ParseWithPreprocessor(In2001("module m (input wire a, output wire y);\n"
                                   "  event logic;\n"
                                   "  reg   result;\n"
                                   "  and   interface (y, a, a);\n"
                                   "  function bit;\n"
                                   "    input x;\n"
                                   "    bit = ~x;\n"
                                   "  endfunction\n"
                                   "  initial begin\n"
                                   "    -> logic;\n"
                                   "    result = bit(1'b0);\n"
                                   "  end\n"
                                   "endmodule\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto& items = r.cu->modules[0]->items;
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kVarDecl, "logic"));
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kFunctionDecl, "bit"));

  auto* gate = FindGateByKind(items, GateKind::kAnd);
  ASSERT_NE(gate, nullptr);
  EXPECT_EQ(gate->gate_inst_name, "interface");
}

TEST(CompilerDirectiveParsing, WordOutsideVerilog2001ListIsNotAKeyword) {
  auto as_net =
      ParseWithPreprocessor(In2001("module m;\n  uwire w;\n"
                                   "endmodule\n"));
  ASSERT_NE(as_net.cu, nullptr);
  auto* as_net_item = as_net.cu->modules[0]->items[0];
  EXPECT_EQ(as_net_item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(as_net_item->data_type.type_name, "uwire");
  EXPECT_TRUE(as_net_item->type_name_undeclared_at_parse);
  EXPECT_TRUE(ParseWithPreprocessorOk("module m;\n  uwire w;\nendmodule\n"));

  auto as_type =
      ParseWithPreprocessor(In2001("module m;\n  logic [7:0] v;\n"
                                   "endmodule\n"));
  EXPECT_TRUE(ReportedError(as_type.diags, "expected ';', got '['",
                            LineInRegion(2), "6.8"));
  EXPECT_TRUE(
      ParseWithPreprocessorOk("module m;\n  logic [7:0] v;\nendmodule\n"));

  auto as_process =
      ParseWithPreprocessor(In2001("module m;\n"
                                   "  reg r;\n"
                                   "  always_comb r = 1'b0;\n"
                                   "endmodule\n"));
  ASSERT_NE(as_process.cu, nullptr);
  EXPECT_FALSE(as_process.has_errors);
  ASSERT_GE(as_process.cu->modules[0]->items.size(), 2U);
  auto* as_process_item = as_process.cu->modules[0]->items[1];
  EXPECT_EQ(as_process_item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(as_process_item->name, "r");
  EXPECT_EQ(as_process_item->data_type.type_name, "always_comb");
  EXPECT_NE(as_process_item->init_expr, nullptr);
  EXPECT_TRUE(as_process_item->type_name_undeclared_at_parse);

  auto outside = ParseWithPreprocessor(
      "module m;\n  reg r;\n  always_comb r = 1'b0;\nendmodule\n");
  ASSERT_NE(outside.cu, nullptr);
  EXPECT_TRUE(
      HasAlwaysOfKind(outside.cu->modules[0]->items, AlwaysKind::kAlwaysComb));
}

TEST(CompilerDirectiveParsing, Verilog2001AdditionCannotNameAModule) {
  auto as_module =
      ParseWithPreprocessor(In2001("module generate;\n"
                                   "endmodule\n"));
  EXPECT_TRUE(ReportedError(as_module.diags,
                            "expected identifier, got 'generate'",
                            LineInRegion(1), "23.2.1"));
  EXPECT_TRUE(ParseWithPreprocessorOk(In1995("module generate;\nendmodule\n")));

  auto as_instance =
      ParseWithPreprocessor(In2001("module sub;\nendmodule\n"
                                   "module top;\n  sub localparam ();\n"
                                   "endmodule\n"));
  EXPECT_TRUE(ReportedError(as_instance.diags, "expected ';', got 'localparam'",
                            LineInRegion(4), "6.8"));
}

TEST(CompilerDirectiveParsing, Verilog2001WordsAreMatchedCaseSensitively) {
  auto r =
      ParseWithPreprocessor(In2001("module GENERATE;\n"
                                   "  reg [7:0] Localparam;\n"
                                   "  wire      SIGNED;\n"
                                   "  reg [7:0] genvar_;\n"
                                   "  initial Localparam = 8'd1;\n"
                                   "endmodule\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->name, "GENERATE");

  auto& items = r.cu->modules[0]->items;
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kVarDecl, "Localparam"));
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kNetDecl, "SIGNED"));
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kVarDecl, "genvar_"));
}

}  // namespace

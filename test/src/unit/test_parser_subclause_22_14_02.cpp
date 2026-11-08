#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "helpers_included_keyword_parse.h"
#include "helpers_keyword_version.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

bool Parses1995(const std::string& body) {
  return ParseWithPreprocessorOk(In1995(body));
}

TEST(CompilerDirectiveParsing, Verilog1995FreedWordNamesDeclaredEntities) {
  ExpectFreedWordsNameDeclaredEntities("1364-1995");
}

TEST(CompilerDirectiveParsing,
     Verilog1995FreedWordIsAnOperandAndAssignmentTarget) {
  ExpectFreedWordIsAnOperandAndAssignmentTarget("1364-1995");
}

TEST(CompilerDirectiveParsing, Verilog1995GateKeywordsInstantiateGates) {
  auto r =
      ParseWithPreprocessor(In1995("module m;\n"
                                   "  reg a, b;\n"
                                   "  wire y, z, w;\n"
                                   "  and  g1 (y, a, b);\n"
                                   "  nor  g2 (z, a, b);\n"
                                   "  buf  (strong1, weak0) g3 (w, a);\n"
                                   "  pmos g4 (w, a, b);\n"
                                   "endmodule\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto& items = r.cu->modules[0]->items;
  EXPECT_NE(FindGateByKind(items, GateKind::kAnd), nullptr);
  EXPECT_NE(FindGateByKind(items, GateKind::kNor), nullptr);
  EXPECT_NE(FindGateByKind(items, GateKind::kBuf), nullptr);
  EXPECT_NE(FindGateByKind(items, GateKind::kPmos), nullptr);
}

TEST(CompilerDirectiveParsing, Verilog1995SwitchPrimitivesInstantiate) {
  auto r =
      ParseWithPreprocessor(In1995("module m;\n"
                                   "  wire a, b, c, d;\n"
                                   "  reg  ctl, nctl, pctl;\n"
                                   "  cmos     s1  (a, b, nctl, pctl);\n"
                                   "  rcmos    s2  (a, b, nctl, pctl);\n"
                                   "  nmos     s3  (c, b, ctl);\n"
                                   "  rnmos    s4  (c, b, ctl);\n"
                                   "  rpmos    s5  (d, b, ctl);\n"
                                   "  tran     s6  (a, c);\n"
                                   "  rtran    s7  (a, d);\n"
                                   "  tranif0  s8  (b, c, ctl);\n"
                                   "  tranif1  s9  (b, d, ctl);\n"
                                   "  rtranif0 s10 (c, d, ctl);\n"
                                   "  rtranif1 s11 (a, b, ctl);\n"
                                   "endmodule\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto& items = r.cu->modules[0]->items;
  const GateKind kExpected[] = {
      GateKind::kCmos,     GateKind::kRcmos,    GateKind::kNmos,
      GateKind::kRnmos,    GateKind::kRpmos,    GateKind::kTran,
      GateKind::kRtran,    GateKind::kTranif0,  GateKind::kTranif1,
      GateKind::kRtranif0, GateKind::kRtranif1,
  };
  for (auto kind : kExpected) {
    EXPECT_NE(FindGateByKind(items, kind), nullptr)
        << "gate kind " << static_cast<int>(kind);
  }
}

TEST(CompilerDirectiveParsing, RemainingVerilog1995GatesInstantiate) {
  auto r = ParseWithPreprocessor(
      In1995("module m;\n"
             "  reg a, b, e;\n"
             "  wire y1, y2, y3, y4, y5, y6, y7, y8, y9, p0, p1;\n"
             "  nand   g1 (y1, a, b);\n"
             "  xor    g2 (y2, a, b);\n"
             "  xnor   g3 (y3, a, b);\n"
             "  or     g4 (y4, a, b);\n"
             "  not    g5 (y5, a);\n"
             "  bufif0 g6 (y6, a, e);\n"
             "  bufif1 g7 (y7, a, e);\n"
             "  notif0 g8 (y8, a, e);\n"
             "  notif1 g9 (y9, a, e);\n"
             "  pullup   u1 (p0);\n"
             "  pulldown d1 (p1);\n"
             "endmodule\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto& items = r.cu->modules[0]->items;
  const GateKind kExpected[] = {
      GateKind::kNand,   GateKind::kXor,      GateKind::kXnor,
      GateKind::kOr,     GateKind::kNot,      GateKind::kBufif0,
      GateKind::kBufif1, GateKind::kNotif0,   GateKind::kNotif1,
      GateKind::kPullup, GateKind::kPulldown,
  };
  for (auto kind : kExpected) {
    EXPECT_NE(FindGateByKind(items, kind), nullptr)
        << "gate kind " << static_cast<int>(kind);
  }
}

TEST(CompilerDirectiveParsing, Verilog1995StrengthKeywordsAreAccepted) {
  EXPECT_TRUE(
      Parses1995("module m;\n"
                 "  reg a;\n"
                 "  wire w1, w2, w3, w4;\n"
                 "  buf (strong0, weak1) g1 (w1, a);\n"
                 "  buf (strong1, weak0) g2 (w2, a);\n"
                 "  buf (pull1, highz0)  g3 (w3, a);\n"
                 "  buf (highz1, pull0)  g4 (w4, a);\n"
                 "  trireg (small)  t1;\n"
                 "  trireg (medium) t2;\n"
                 "  trireg (large)  t3;\n"
                 "endmodule\n"));
}

TEST(CompilerDirectiveParsing,
     Verilog1995EventAndBranchKeywordsOpenStatements) {
  auto r =
      ParseWithPreprocessor(In1995("module m;\n"
                                   "  reg clk, rst, go;\n"
                                   "  reg [7:0] q;\n"
                                   "  always @(posedge clk or negedge rst)\n"
                                   "    if (!rst) q <= 8'd0;\n"
                                   "    else q <= q + 8'd1;\n"
                                   "  initial begin : blk\n"
                                   "    wait (go);\n"
                                   "    forever #1 q <= q;\n"
                                   "  end\n"
                                   "endmodule\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto* always_item = FirstAlwaysItem(r);
  ASSERT_NE(always_item, nullptr);
  ASSERT_EQ(always_item->sensitivity.size(), 2u);
  EXPECT_EQ(always_item->sensitivity[0].edge, Edge::kPosedge);
  EXPECT_EQ(always_item->sensitivity[1].edge, Edge::kNegedge);
  ASSERT_NE(always_item->body, nullptr);
  EXPECT_EQ(always_item->body->kind, StmtKind::kIf);
  EXPECT_NE(always_item->body->else_branch, nullptr);
}

TEST(CompilerDirectiveParsing, RemainingVerilog1995KeywordRolesAreAccepted) {
  auto r = ParseWithPreprocessor(
      In1995("module sub (inout wire b, input wire a, input wire e,\n"
             "            output wire y);\n"
             "  parameter p = 1;\n"
             "  assign y = a;\n"
             "  specify\n"
             "    if (e) (a => y) = 2;\n"
             "    ifnone (a => y) = 1;\n"
             "  endspecify\n"
             "endmodule\n"
             "module top;\n"
             "  wire bb, aa, ee, yy;\n"
             "  sub u (bb, aa, ee, yy);\n"
             "  defparam u.p = 43;\n"
             "  reg r;\n"
             "  function invert;\n"
             "    input x;\n"
             "    invert = ~x;\n"
             "  endfunction\n"
             "  initial r = invert(1'b0);\n"
             "endmodule\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);

  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInout);
  EXPECT_NE(FindSpecifyBlock(r.cu->modules[0]->items), nullptr);

  auto& top_items = r.cu->modules[1]->items;
  EXPECT_NE(FindItemByKind(top_items, ModuleItemKind::kDefparam), nullptr);
  EXPECT_TRUE(
      HasItemKindNamed(top_items, ModuleItemKind::kFunctionDecl, "invert"));
}

TEST(CompilerDirectiveParsing, Verilog1995NetTypeKeywordsDeclareNets) {
  EXPECT_TRUE(
      Parses1995("module m;\n"
                 "  wand  w1;\n"
                 "  wor   w2;\n"
                 "  triand t1;\n"
                 "  trior  t2;\n"
                 "  tri0   t3;\n"
                 "  tri1   t4;\n"
                 "  trireg (large) t5;\n"
                 "  supply0 s0;\n"
                 "  supply1 s1;\n"
                 "  wire scalared [1:0] v1;\n"
                 "  wire vectored [1:0] v2;\n"
                 "endmodule\n"));
}

TEST(CompilerDirectiveParsing, Verilog1995SpecifyKeywordsOpenABlock) {
  auto r = ParseWithPreprocessor(
      In1995("macromodule m (input wire a, output wire y);\n"
             "  assign y = a;\n"
             "  specify\n"
             "    specparam tr = 1;\n"
             "    (a => y) = tr;\n"
             "  endspecify\n"
             "endmodule\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_NE(FindSpecifyBlock(r.cu->modules[0]->items), nullptr);
}

TEST(CompilerDirectiveParsing, Verilog1995PrimitiveKeywordsDeclareAUdp) {
  EXPECT_TRUE(
      Parses1995("primitive p (out, in);\n"
                 "  output out;\n"
                 "  input in;\n"
                 "  table\n"
                 "    0 : 1;\n"
                 "    1 : 0;\n"
                 "  endtable\n"
                 "endprimitive\n"));
}

TEST(CompilerDirectiveParsing, Verilog1995ProceduralKeywordsOpenStatements) {
  EXPECT_TRUE(
      Parses1995("module m;\n"
                 "  reg a, b;\n"
                 "  integer i;\n"
                 "  event ev;\n"
                 "  initial begin\n"
                 "    for (i = 0; i < 2; i = i + 1) a = 1'b0;\n"
                 "    while (i > 0) i = i - 1;\n"
                 "    repeat (2) b = 1'b1;\n"
                 "    casez (a)\n"
                 "      1'b0: b = 1'b1;\n"
                 "      default: b = 1'b0;\n"
                 "    endcase\n"
                 "    casex (a)\n"
                 "      1'bx: b = 1'b1;\n"
                 "      default: b = 1'b0;\n"
                 "    endcase\n"
                 "    fork\n"
                 "      a = 1'b1;\n"
                 "    join\n"
                 "    -> ev;\n"
                 "    force a = 1'b1;\n"
                 "    release a;\n"
                 "    assign b = a;\n"
                 "    deassign b;\n"
                 "    disable m;\n"
                 "  end\n"
                 "endmodule\n"));
}

TEST(CompilerDirectiveParsing,
     Verilog1995FreedWordNamesEveryOtherDeclarationKind) {
  auto r =
      ParseWithPreprocessor(In1995("module m (input wire a, output wire y);\n"
                                   "  event logic;\n"
                                   "  reg   result;\n"
                                   "  and   interface (y, a, a);\n"
                                   "  function bit;\n"
                                   "    input x;\n"
                                   "    bit = ~x;\n"
                                   "  endfunction\n"
                                   "  specify\n"
                                   "    specparam byte = 1;\n"
                                   "    (a => y) = byte;\n"
                                   "  endspecify\n"
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
  EXPECT_NE(FindSpecifyBlock(items), nullptr);
}

TEST(CompilerDirectiveParsing, ConstantKeywordsOutsideTheListAreIdentifiers) {
  EXPECT_TRUE(
      Parses1995("module m;\n"
                 "  parameter P = 8;\n"
                 "  reg [P-1:0] v;\n"
                 "endmodule\n"));

  auto as_localparam =
      ParseWithPreprocessor(In1995("module m;\n"
                                   "  localparam Q = 8;\n"
                                   "endmodule\n"));
  ASSERT_NE(as_localparam.cu, nullptr);
  EXPECT_FALSE(as_localparam.has_errors);
  ASSERT_EQ(as_localparam.cu->modules[0]->items.size(), 1u);
  auto* localparam_item = as_localparam.cu->modules[0]->items[0];
  EXPECT_EQ(localparam_item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(localparam_item->name, "Q");
  EXPECT_FALSE(localparam_item->is_localparam);
  EXPECT_EQ(localparam_item->data_type.type_name, "localparam");
  EXPECT_TRUE(localparam_item->type_name_undeclared_at_parse);

  auto as_genvar =
      ParseWithPreprocessor(In1995("module m;\n"
                                   "  genvar i;\n"
                                   "endmodule\n"));
  ASSERT_NE(as_genvar.cu, nullptr);
  EXPECT_FALSE(as_genvar.has_errors);
  auto* genvar_item = as_genvar.cu->modules[0]->items[0];
  EXPECT_EQ(genvar_item->kind, ModuleItemKind::kVarDecl);
  EXPECT_FALSE(genvar_item->is_genvar);
  EXPECT_EQ(genvar_item->data_type.type_name, "genvar");
  EXPECT_TRUE(genvar_item->type_name_undeclared_at_parse);

  auto r =
      ParseWithPreprocessor(In1995("module m;\n"
                                   "  reg [7:0] localparam;\n"
                                   "  reg [7:0] genvar;\n"
                                   "  reg [7:0] generate;\n"
                                   "endmodule\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kVarDecl, "localparam"));
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kVarDecl, "genvar"));
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kVarDecl, "generate"));
}

TEST(CompilerDirectiveParsing, ReservedWordsAreMatchedCaseSensitively) {
  auto r =
      ParseWithPreprocessor(In1995("module MODULE;\n"
                                   "  reg [7:0] REG;\n"
                                   "  wire      Wire;\n"
                                   "  initial REG = 8'd1;\n"
                                   "endmodule\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->name, "MODULE");

  auto& items = r.cu->modules[0]->items;
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kVarDecl, "REG"));
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kNetDecl, "Wire"));
}

TEST(CompilerDirectiveParsing, ReservedWordCannotNameAVariable) {
  auto as_wire = ParseWithPreprocessor(In1995(VarDecl("wire")));
  EXPECT_TRUE(ReportedError(as_wire.diags, "expected identifier, got 'wire'",
                            LineInRegion(2), "6.8"));
  auto as_trireg = ParseWithPreprocessor(In1995(VarDecl("trireg")));
  EXPECT_TRUE(ReportedError(as_trireg.diags,
                            "expected identifier, got 'trireg'",
                            LineInRegion(2), "6.8"));
}

TEST(CompilerDirectiveParsing, ReservedWordCannotNameAModule) {
  auto r = ParseWithPreprocessor(In1995("module always;\nendmodule\n"));
  EXPECT_TRUE(ReportedError(r.diags, "expected identifier, got 'always'",
                            LineInRegion(1), "23.2.1"));
}

TEST(CompilerDirectiveParsing, WordOutsideVerilog1995ListIsNotAKeyword) {
  auto as_type =
      ParseWithPreprocessor(In1995("module m;\n"
                                   "  logic [7:0] v;\n"
                                   "endmodule\n"));
  EXPECT_TRUE(ReportedError(as_type.diags, "expected ';', got '['",
                            LineInRegion(2), "6.8"));
  EXPECT_TRUE(
      ParseWithPreprocessorOk("module m;\n"
                              "  logic [7:0] v;\n"
                              "endmodule\n"));

  auto as_process =
      ParseWithPreprocessor(In1995("module m;\n"
                                   "  reg r;\n"
                                   "  always_comb r = 1'b0;\n"
                                   "endmodule\n"));
  ASSERT_NE(as_process.cu, nullptr);
  EXPECT_FALSE(as_process.has_errors);
  ASSERT_EQ(as_process.cu->modules[0]->items.size(), 2u);
  auto* process_item = as_process.cu->modules[0]->items[1];
  EXPECT_EQ(process_item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(process_item->name, "r");
  EXPECT_EQ(process_item->data_type.type_name, "always_comb");
  EXPECT_TRUE(process_item->type_name_undeclared_at_parse);
}

}  // namespace

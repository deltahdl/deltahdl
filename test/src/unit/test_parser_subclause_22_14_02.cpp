#include "fixture_parser.h"
#include "helpers_included_keyword_parse.h"
#include "helpers_keyword_version.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

bool Parses1995(const std::string& body) {
  return ParseWithPreprocessorOk(In1995(body));
}

// A word Table 22-1 omits is an ordinary identifier, so it can name anything
// an identifier names. Declarations are only the most obvious position: this
// runs one word from a later standard through the module name, both port
// names, a parameter, a net, a variable, a task, a named block, and an
// instance name, and reads each back off the parsed tree. The `1364-2001`
// version specifier gets the same treatment in the sibling file for §22.14.3.
TEST(CompilerDirectiveParsing, Verilog1995FreedWordNamesDeclaredEntities) {
  ExpectFreedWordsNameDeclaredEntities("1364-1995");
}

// The same freed word as an expression operand and as the target of a
// procedural assignment — positions that carry a value rather than introduce a
// name, and so reach the parser by a different path than a declaration does.
// The `1364-2001` version specifier gets the same treatment in the sibling
// file for §22.14.3.
TEST(CompilerDirectiveParsing,
     Verilog1995FreedWordIsAnOperandAndAssignmentTarget) {
  ExpectFreedWordIsAnOperandAndAssignmentTarget("1364-1995");
}

// Table 22-1 lists the gate primitives and drive strengths, and under this
// list they still open a gate instantiation rather than name one.
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

// The switch and transmission primitives. Table 22-1 lists eleven of them
// beyond the logic gates above, each opening its own instantiation form, and
// none is a word any later standard touched — so under this list they have to
// behave exactly as they do under the default one.
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

// The logic gates and pull gates Table 22-1 lists that the instantiation test
// above does not reach. Between the two, every gate primitive the 1995 list
// reserves is observed opening an instantiation under that list.
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

// Table 22-1 reserves the strength words as well as the constructs they
// modify: all eight drive strengths and all three charge strengths. They are a
// separate syntactic position from the gate name itself, so they are worth
// driving through the parser in that position rather than only as tokens.
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

// The event-control and branching words: an `always` procedure sensitive to a
// `posedge`/`negedge` list joined by `or`, an `if`/`else` pair, a `forever`
// loop, and a `wait`. Each is a Table 22-1 entry occupying a position none of
// the declaration or instantiation tests above reaches.
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

// `function`/`endfunction`, `defparam`, `inout`, and the specify-block
// `ifnone` — the last Table 22-1 words with a syntactic role none of the other
// tests here exercises.
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

// The net type keywords of Table 22-1, each one still introducing a net of its
// own type. `scalared` and `vectored` ride along on the same declarations.
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

// `specify`, `endspecify`, `specparam`, and `edge` are all Table 22-1 words,
// and the block they build is a §22.14.2-era construct in its own right.
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

// `primitive`/`table`/`endtable`/`endprimitive` — the user-defined primitive
// keywords, which no later standard changed and which Table 22-1 lists.
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

// The procedural keywords: the loops, the case forms, the parallel block, and
// the assignment-control words. All are Table 22-1 entries, so all still open
// statements under this list.
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

// The declaration kinds the other freed-word tests do not reach: an event, a
// function, a gate instance name, and a specparam inside a specify block.
// Each is a distinct declaration production, so a freed word has to survive
// each one separately rather than only the net and variable forms. The
// `1364-2001` version specifier gets the same treatment in the sibling file
// for §22.14.3.
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

// The constant-declaration keywords split across the list boundary: `parameter`
// is a Table 22-1 word and still declares a constant, while `localparam`,
// `genvar`, and `generate` arrived in a later standard and so carry no keyword
// meaning here. Both halves matter — the words are rejected in the keyword
// position and accepted in the identifier position, which is what distinguishes
// "not reserved" from "not understood".
TEST(CompilerDirectiveParsing, ConstantKeywordsOutsideTheListAreIdentifiers) {
  EXPECT_TRUE(
      Parses1995("module m;\n"
                 "  parameter P = 8;\n"
                 "  reg [P-1:0] v;\n"
                 "endmodule\n"));

  // §23.3.2 owns both reports, not §22.14: with the word an ordinary
  // identifier the two names read as a module name and an instance name, so
  // Parser::ParseImplicitTypeOrInst hands them to Parser::ParseModuleInstList
  // and that demands the port connection list at src/parser/parser_inst.cpp:78.
  auto as_localparam =
      ParseWithPreprocessor(In1995("module m;\n"
                                   "  localparam Q = 8;\n"
                                   "endmodule\n"));
  EXPECT_TRUE(ReportedError(as_localparam.diags, "expected '(', got '='",
                            LineInRegion(2), "23.3.2"));

  auto as_genvar = ParseWithPreprocessor(
      In1995("module m;\n"
             "  genvar i;\n"
             "  generate\n"
             "    for (i = 0; i < 2; i = i + 1) begin : g\n"
             "    end\n"
             "  endgenerate\n"
             "endmodule\n"));
  EXPECT_TRUE(ReportedError(as_genvar.diags, "expected '(', got ';'",
                            LineInRegion(2), "23.3.2"));

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

// The list names particular spellings, and the language distinguishes case, so
// a word that differs from a listed one only in case falls outside the list and
// is free to name something. This is the exclusivity rule at its narrowest
// margin.
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

// Negative: a word Table 22-1 lists is reserved, so it cannot be the
// identifier in a declaration. This is the direct counterpart of the freed-word
// tests above — the same syntactic slot, a word from the other side of the
// list.
TEST(CompilerDirectiveParsing, ReservedWordCannotNameAVariable) {
  // §6.8 owns the report, not §22.14: the word stands where
  // Parser::ParseVarDeclList reads the declared name of a variable at
  // src/parser/parser_types.cpp:584. TokenKindName answers "token" for every
  // keyword (#3089), so the message cannot say which word was rejected.
  auto as_wire = ParseWithPreprocessor(In1995(VarDecl("wire")));
  EXPECT_TRUE(ReportedError(as_wire.diags, "expected identifier, got token",
                            LineInRegion(2), "6.8"));
  auto as_trireg = ParseWithPreprocessor(In1995(VarDecl("trireg")));
  EXPECT_TRUE(ReportedError(as_trireg.diags, "expected identifier, got token",
                            LineInRegion(2), "6.8"));
}

TEST(CompilerDirectiveParsing, ReservedWordCannotNameAModule) {
  // §23.2.1 owns the report on the module name: the word stands where
  // Parser::ParseModuleDecl reads it at src/parser/parser.cpp:652.
  auto r = ParseWithPreprocessor(In1995("module always;\nendmodule\n"));
  EXPECT_TRUE(ReportedError(r.diags, "expected identifier, got token",
                            LineInRegion(1), "23.2.1"));
}

// Negative from the other direction: a word Table 22-1 omits is not reserved,
// so it cannot act as a keyword either. `logic` as a data type and
// `always_comb` as a block header both fail under this list, though both are
// accepted under the default one.
TEST(CompilerDirectiveParsing, WordOutsideVerilog1995ListIsNotAKeyword) {
  // §6.8 owns this report: with `logic` an ordinary identifier the packed
  // dimension is where the declaration was meant to end, so
  // Parser::ParsePlainVarDecl demands the semicolon at
  // src/parser/parser_items.cpp:712.
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

  // §23.3.2 owns this one instead: two identifiers read as a module name and
  // an instance name, so Parser::ParseModuleInstList is looking for the port
  // connection list.
  auto as_process =
      ParseWithPreprocessor(In1995("module m;\n"
                                   "  reg r;\n"
                                   "  always_comb r = 1'b0;\n"
                                   "endmodule\n"));
  EXPECT_TRUE(ReportedError(as_process.diags, "expected '(', got '='",
                            LineInRegion(3), "23.3.2"));
}

}  // namespace

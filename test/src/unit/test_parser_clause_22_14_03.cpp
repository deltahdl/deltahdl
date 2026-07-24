#include <cstddef>
#include <string>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// Table 22-2: the identifiers "1364-2001" adds to the list it inherits.
constexpr const char* kTable222[] = {
    "automatic",
    "cell",
    "config",
    "design",
    "endconfig",
    "endgenerate",
    "generate",
    "genvar",
    "incdir",
    "include",
    "instance",
    "liblist",
    "library",
    "localparam",
    "noshowcancelled",
    "pulsestyle_ondetect",
    "pulsestyle_onevent",
    "showcancelled",
    "signed",
    "unsigned",
    "use",
};

// Table 22-1, the list this version includes whole.
constexpr const char* kTable221[] = {
    "always",    "and",          "assign",     "begin",     "buf",
    "bufif0",    "bufif1",       "case",       "casex",     "casez",
    "cmos",      "deassign",     "default",    "defparam",  "disable",
    "edge",      "else",         "end",        "endcase",   "endfunction",
    "endmodule", "endprimitive", "endspecify", "endtable",  "endtask",
    "event",     "for",          "force",      "forever",   "fork",
    "function",  "highz0",       "highz1",     "if",        "ifnone",
    "initial",   "inout",        "input",      "integer",   "join",
    "large",     "macromodule",  "medium",     "module",    "nand",
    "negedge",   "nmos",         "nor",        "not",       "notif0",
    "notif1",    "or",           "output",     "parameter", "pmos",
    "posedge",   "primitive",    "pull0",      "pull1",     "pulldown",
    "pullup",    "rcmos",        "real",       "realtime",  "reg",
    "release",   "repeat",       "rnmos",      "rpmos",     "rtran",
    "rtranif0",  "rtranif1",     "scalared",   "small",     "specify",
    "specparam", "strong0",      "strong1",    "supply0",   "supply1",
    "table",     "task",         "time",       "tran",      "tranif0",
    "tranif1",   "tri",          "tri0",       "tri1",      "triand",
    "trior",     "trireg",       "vectored",   "wait",      "wand",
    "weak0",     "weak1",        "while",      "wire",      "wor",
    "xnor",      "xor",
};

// Wraps `body` in a `begin_keywords "1364-2001" region so this version's
// reserved word list governs it, and parses it through the preprocessor -- the
// directive is real source, and the version marker the preprocessor emits is
// what the lexer reads.
std::string In2001(const std::string& body) {
  return "`begin_keywords \"1364-2001\"\n" + body + "`end_keywords\n";
}

std::string In1995(const std::string& body) {
  return "`begin_keywords \"1364-1995\"\n" + body + "`end_keywords\n";
}

bool Parses2001(const std::string& body) {
  return ParseWithPreprocessorOk(In2001(body));
}

// Every word Table 22-2 lists is reserved under this version, so none of them
// can occupy the identifier slot of a declaration. The 1364-1995 leg is what
// makes each one an *addition* rather than an inheritance: the same
// declaration, the same word, and the list this version builds on accepts it.
// Run through real source so the rejection is the reserved word list's doing
// and not some unrelated parse failure.
TEST(CompilerDirectiveParsing, Verilog2001AdditionsCannotNameAVariable) {
  for (const char* word : kTable222) {
    std::string decl =
        std::string("module m;\n  reg [7:0] ") + word + ";\nendmodule\n";
    EXPECT_FALSE(ParseWithPreprocessorOk(In2001(decl)))
        << word << " is reserved by Table 22-2";
    EXPECT_TRUE(ParseWithPreprocessorOk(In1995(decl)))
        << word << " is not in the list this version extends";
  }
}

// The negative form of the inclusion half, swept over the whole inherited
// list. The role tests below show those words still opening the constructs
// they always did; this shows the other side of the same claim, that none of
// them has been freed to name something. Sweeping all 102 is what makes the
// inherited table, rather than the handful of its entries a role test happens
// to reach, the thing being checked.
TEST(CompilerDirectiveParsing, InheritedKeywordsCannotNameAVariable) {
  EXPECT_EQ(std::size(kTable221), 102u);
  for (const char* word : kTable221) {
    std::string decl =
        std::string("module m;\n  reg [7:0] ") + word + ";\nendmodule\n";
    EXPECT_FALSE(ParseWithPreprocessorOk(In2001(decl)))
        << word << " is carried over from Table 22-1 and stays reserved";
  }
}

// The constant-declaration keywords this version adds, each doing its own job.
// `localparam` declares a constant, `genvar`/`generate`/`endgenerate` build a
// loop generate construct, and `automatic` qualifies a function. Under the
// list this version extends none of these is a keyword at all, so this is the
// clearest place the addition shows up as behaviour rather than as a token.
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

// `signed` and `unsigned` are additions of this version, and they are
// modifiers rather than declaration openers -- a separate syntactic position
// from the constant keywords above. Here they qualify a port, a parameter, a
// net, a variable, and a function return type.
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

// `automatic` on a task as well as on a function -- the other declaration this
// addition qualifies.
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

// The pulse-control additions occupy a position none of the other tests
// reaches: they are specify block items, so they only have a keyword role
// inside a specify block that Table 22-1's own words open.
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

// The inclusion half at this stage: the words carried over from the earlier
// list still open the constructs they always did -- gate and switch
// primitives, drive and charge strengths, the net types, a specify block, a
// user-defined primitive, and the procedural statements.
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

// The specify, specparam, and user-defined primitive keywords of the inherited
// list, which the combined statement test above does not reach.
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

// A word neither table lists is an ordinary identifier, so it can name
// anything an identifier names. Declarations are only the most obvious
// position: this runs words from later standards through the module name, both
// port names, a parameter, a net, a variable, a task, a named block, and an
// instance name, and reads each back off the parsed tree.
TEST(CompilerDirectiveParsing, FreedWordNamesDeclaredEntities) {
  auto r = ParseWithPreprocessor(
      In2001("module bit (input wire logic, output wire byte);\n"
             "  parameter int = 4;\n"
             "  wire [7:0] string;\n"
             "  reg  [7:0] longint;\n"
             "  task shortint; begin longint = 8'd9; end endtask\n"
             "  initial begin : local\n"
             "    shortint;\n"
             "  end\n"
             "  assign byte = logic;\n"
             "endmodule\n"
             "module top;\n"
             "  wire a, b;\n"
             "  bit interface (.logic(a), .byte(b));\n"
             "endmodule\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);

  auto* m = r.cu->modules[0];
  EXPECT_EQ(m->name, "bit");
  ASSERT_EQ(m->ports.size(), 2u);
  EXPECT_EQ(m->ports[0].name, "logic");
  EXPECT_EQ(m->ports[1].name, "byte");
  EXPECT_TRUE(HasItemKindNamed(m->items, ModuleItemKind::kParamDecl, "int"));
  EXPECT_TRUE(HasItemKindNamed(m->items, ModuleItemKind::kNetDecl, "string"));
  EXPECT_TRUE(HasItemKindNamed(m->items, ModuleItemKind::kVarDecl, "longint"));
  EXPECT_TRUE(
      HasItemKindNamed(m->items, ModuleItemKind::kTaskDecl, "shortint"));

  auto* u =
      FindItemByKind(r.cu->modules[1]->items, ModuleItemKind::kModuleInst);
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(u->inst_module, "bit");
  EXPECT_EQ(u->inst_name, "interface");
}

// The same freed word as an expression operand and as the target of a
// procedural assignment -- positions that carry a value rather than introduce
// a name, and so reach the parser by a different path than a declaration does.
TEST(CompilerDirectiveParsing, FreedWordIsAnOperandAndAssignmentTarget) {
  auto r =
      ParseWithPreprocessor(In2001("module m;\n"
                                   "  reg [7:0] logic;\n"
                                   "  reg [7:0] result;\n"
                                   "  initial begin\n"
                                   "    logic = 8'd5;\n"
                                   "    result = logic + 8'd1;\n"
                                   "  end\n"
                                   "endmodule\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto* first = NthInitialStmt(r, 0);
  ASSERT_NE(first, nullptr);
  ASSERT_NE(first->lhs, nullptr);
  EXPECT_EQ(first->lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(first->lhs->text, "logic");

  auto* second = NthInitialStmt(r, 1);
  ASSERT_NE(second, nullptr);
  ASSERT_NE(second->rhs, nullptr);
  EXPECT_EQ(second->rhs->kind, ExprKind::kBinary);
  ASSERT_NE(second->rhs->lhs, nullptr);
  EXPECT_EQ(second->rhs->lhs->text, "logic");
}

// The declaration kinds the other freed-word test does not reach: an event, a
// function, and a gate instance name. Each is a distinct declaration
// production, so a freed word has to survive each one separately.
TEST(CompilerDirectiveParsing, FreedWordNamesEveryOtherDeclarationKind) {
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

// The negative from the other direction: a word neither table lists is not
// reserved, so it carries no keyword meaning either. `uwire` is the sharpest
// case -- it is the sole word the very next version adds, so it is the closest
// reserved word to this list without being in it. Each case is paired with the
// same source outside the region, which is what shows the region and not some
// unrelated limitation is doing the rejecting.
TEST(CompilerDirectiveParsing, WordOutsideVerilog2001ListIsNotAKeyword) {
  EXPECT_FALSE(Parses2001("module m;\n  uwire w;\nendmodule\n"));
  EXPECT_TRUE(ParseWithPreprocessorOk("module m;\n  uwire w;\nendmodule\n"));

  EXPECT_FALSE(Parses2001("module m;\n  logic [7:0] v;\nendmodule\n"));
  EXPECT_TRUE(
      ParseWithPreprocessorOk("module m;\n  logic [7:0] v;\nendmodule\n"));

  EXPECT_FALSE(
      Parses2001("module m;\n"
                 "  reg r;\n"
                 "  always_comb r = 1'b0;\n"
                 "endmodule\n"));
}

// A word this version reserves cannot name a module or an instance either --
// the same rule in the two positions the variable sweep above does not cover.
TEST(CompilerDirectiveParsing, Verilog2001AdditionCannotNameAModule) {
  EXPECT_FALSE(Parses2001("module generate;\nendmodule\n"));
  EXPECT_TRUE(ParseWithPreprocessorOk(In1995("module generate;\nendmodule\n")));
  EXPECT_FALSE(
      Parses2001("module sub;\nendmodule\n"
                 "module top;\n  sub localparam ();\nendmodule\n"));
}

// The tables name particular spellings, and the language distinguishes case,
// so a word differing from a listed one only in case falls outside the list and
// is free to name something. This is the exclusivity rule at its narrowest
// margin, in the positions where it matters most.
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

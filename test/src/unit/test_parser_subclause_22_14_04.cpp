#include <cstddef>
#include <iterator>
#include <string>

#include "fixture_parser.h"
#include "helpers_keyword_version.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "model_keyword_tables.h"

using namespace delta;

namespace {

// The ten identifiers this version_specifier drops from what "1364-2001"
// reserves.
constexpr const char* kExcluded[] = {
    "cell",    "config",   "design",  "endconfig", "incdir",
    "include", "instance", "liblist", "library",   "use",
};

// The rest of Table 22-2, which this version keeps reserved.
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
// The exception itself, swept over all ten and paired with the version it is
// taken from. Being excluded from the reserved list means being an ordinary
// identifier, so each word has to occupy the identifier slot of a declaration
// here while the very same declaration is rejected under "1364-2001". One leg
// alone would prove nothing: the accepting leg could be any parse that
// happens to succeed, and the rejecting leg could be any unrelated failure.
TEST(CompilerDirectiveParsing, NoconfigExcludedWordsCanNameAVariable) {
  EXPECT_EQ(std::size(kExcluded), 10u);
  for (const char* word : kExcluded) {
    EXPECT_TRUE(ParseWithPreprocessorOk(InNoconfig(VarDecl(word))))
        << word << " is dropped from the reserved list by this version";
    // §6.8 owns the report: VarDecl heads its declaration with `reg`, so the
    // word stands where Parser::ParseVarDeclList reads a variable's name.
    // TokenKindName answers "token" for most keywords (#3089), so the word
    // under test is told apart by the failure message rather than by the
    // report.
    auto r = ParseWithPreprocessor(In2001(VarDecl(word)));
    EXPECT_TRUE(ReportedError(r.diags, "expected identifier, got ",
                              LineInRegion(2), "6.8"))
        << word << " is reserved by the version this one is defined from";
  }
}

// The complement of the exception: the eleven entries of Table 22-2 it does
// not name stay reserved, so none of them can name a variable. The 1364-1995
// leg is what keeps this from being an unrelated parse failure -- under the
// list "1364-2001" extends, the same declaration is accepted.
TEST(CompilerDirectiveParsing, NoconfigKeepsOtherVerilog2001AdditionsReserved) {
  EXPECT_EQ(std::size(kKept), 11u);
  for (const char* word : kKept) {
    auto r = ParseWithPreprocessor(InNoconfig(VarDecl(word)));
    EXPECT_TRUE(ReportedError(r.diags, "expected identifier, got ",
                              LineInRegion(2), "6.8"))
        << word << " is not among the ten this version drops";
    EXPECT_TRUE(ParseWithPreprocessorOk(In1995(VarDecl(word))))
        << word << " is an addition of 1364-2001, not of the list it extends";
  }
}

// The inherited list is outside the exception's reach, so all 102 of Table
// 22-1's entries stay reserved under this version. Sweeping the whole table is
// what makes the inheritance, rather than a handful of its entries, the thing
// being checked.
TEST(CompilerDirectiveParsing, NoconfigKeepsAllVerilog1995KeywordsReserved) {
  EXPECT_EQ(std::size(kTable221), 102u);
  for (const char* word : kTable221) {
    auto r = ParseWithPreprocessor(InNoconfig(VarDecl(word)));
    EXPECT_TRUE(ReportedError(r.diags, "expected identifier, got ",
                              LineInRegion(2), "6.8"))
        << word << " is inherited from Table 22-1 and stays reserved";
  }
}

// A declaration is only the most obvious identifier position. This puts all
// ten dropped words through the rest of them at once -- the module name, both
// port names, a parameter, a net, two variables, a task, a named block, and an
// instance name -- and reads each back off the parsed tree, so the words are
// observed naming things rather than merely getting past the lexer.
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

// The same words in positions that carry a value rather than introduce a
// name -- an expression operand and the target of a procedural assignment --
// which reach the parser by a different path than a declaration does.
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

// The declaration kinds the entity sweep above does not reach: an event, a
// function, and a gate instance name, each a distinct production a dropped
// word has to survive in its own right.
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

// A subroutine's formal argument is its own declaration production, reached by
// a different path than any module-level declaration, so a dropped word has to
// survive it in its own right. Here dropped words name a function's argument
// and a task's argument, and each body reads the argument back, so the name has
// to resolve inside the subroutine and not merely be accepted in its header.
// The paired leg rejects the same headers under the version this one is defined
// from, which localizes the acceptance to the exclusion.
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

  // §13.3 owns both reports: a reserved word in a tf_port_item's name slot
  // leaves the item with no port_identifier, which is what
  // Parser::ParseFunctionArgTrailer says.
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

// The dropped words in their *keyword* role rather than in an identifier slot,
// which is where the exclusion has its sharpest consequence. Seven of the ten
// exist to build one construct -- a configuration -- so under "1364-2001" this
// source produces a config declaration, and under this version it cannot be
// written at all: every word opening it has become an ordinary identifier. The
// module alongside it parses under both, which localizes the failure to the
// construct rather than to the source as a whole.
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

  // Under the version this one is defined from, the seven words keep their
  // keyword roles and the declaration is built.
  auto under_2001 = ParseWithPreprocessor(In2001(kSrc));
  ASSERT_NE(under_2001.cu, nullptr);
  EXPECT_FALSE(under_2001.has_errors);
  ASSERT_EQ(under_2001.cu->configs.size(), 1u);
  auto* cfg = under_2001.cu->configs[0];
  EXPECT_EQ(cfg->name, "config_a");
  EXPECT_EQ(cfg->design_cells.size(), 1u);
  EXPECT_EQ(cfg->rules.size(), 3u);

  // Dropping the words from the reserved list takes the construct with them.
  // §3.12.1 owns the report: with `config` an ordinary identifier, line 3 of
  // the source heads nothing the compilation unit admits and
  // Parser::ParseTopLevel says so at src/parser/parser.cpp:499.
  auto dropped = ParseWithPreprocessor(InNoconfig(kSrc));
  EXPECT_TRUE(ReportedError(dropped.diags, "expected top-level declaration",
                            LineInRegion(3), "3.12.1"));

  // The module on its own parses under this version, so the rejection above is
  // the configuration's doing and not a wholesale failure of the region.
  EXPECT_TRUE(ParsesNoconfig("module top;\nendmodule\n"));
}

// The same claim one word at a time: a configuration cannot even be opened
// under this version, and the word that would open it is free to name a
// module instead -- the two halves of the exclusion in one place.
TEST(CompilerDirectiveParsing, NoconfigFreesTheWordThatOpensAConfiguration) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk(In2001("config c;\n"
                                     "  design lib.top;\n"
                                     "endconfig\n")));
  // §3.12.1 owns the report: with `config` an ordinary identifier the first
  // line heads nothing the compilation unit admits, and Parser::ParseTopLevel
  // says so at src/parser/parser.cpp:499.
  auto dropped =
      ParseWithPreprocessor(InNoconfig("config c;\n"
                                       "  design lib.top;\n"
                                       "endconfig\n"));
  EXPECT_TRUE(ReportedError(dropped.diags, "expected top-level declaration",
                            LineInRegion(1), "3.12.1"));

  // The very same word, now naming a design element under this version.
  auto r = ParseWithPreprocessor(InNoconfig("module config;\nendmodule\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "config");
  EXPECT_TRUE(r.cu->configs.empty());
}

// "Behaves similarly to 1364-2001" is a claim about what this version still
// does, not only about what it drops. The eleven kept additions go on opening
// the constructs they open under that version: `localparam` declares a
// constant, `genvar`/`generate`/`endgenerate` build a loop generate construct,
// `automatic` qualifies a subroutine, and `signed`/`unsigned` qualify a
// declaration.
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

// The kept pulse-control additions occupy a position none of the other tests
// reaches: they are specify block items, so their keyword role only exists
// inside a specify block that Table 22-1's own words open.
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

// A dropped word naming a module and an instance -- the two positions the
// variable sweep does not cover -- again paired against the version this one
// is defined from.
TEST(CompilerDirectiveParsing, NoconfigExcludedWordNamesAModule) {
  EXPECT_TRUE(ParsesNoconfig("module config;\nendmodule\n"));
  // §23.2.1 owns the report on the module name: the word stands where
  // Parser::ParseModuleDecl reads it.
  auto as_module = ParseWithPreprocessor(In2001("module config;\nendmodule\n"));
  EXPECT_TRUE(ReportedError(as_module.diags, "expected identifier, got token",
                            LineInRegion(1), "23.2.1"));

  EXPECT_TRUE(
      ParsesNoconfig("module sub;\nendmodule\n"
                     "module top;\n  sub library ();\nendmodule\n"));
  // §6.8 owns the report on the instance name, not §23.3.2: an instantiation
  // is recognized by the identifier following the module name, so
  // Parser::ParseImplicitTypeOrInst hands `sub` to Parser::ParsePlainVarDecl
  // instead and that demands a semicolon at src/parser/parser_items.cpp:712.
  auto as_instance =
      ParseWithPreprocessor(In2001("module sub;\nendmodule\n"
                                   "module top;\n  sub library ();\n"
                                   "endmodule\n"));
  EXPECT_TRUE(ReportedError(as_instance.diags, "expected ';', got token",
                            LineInRegion(4), "6.8"));
}

// A kept word still cannot name a module, which is the same complement claim
// in a position the variable sweep does not reach.
TEST(CompilerDirectiveParsing, NoconfigKeptAdditionCannotNameAModule) {
  // §23.2.1 owns the report on the module name: the word stands where
  // Parser::ParseModuleDecl reads it.
  auto as_module =
      ParseWithPreprocessor(InNoconfig("module generate;\n"
                                       "endmodule\n"));
  EXPECT_TRUE(ReportedError(as_module.diags, "expected identifier, got token",
                            LineInRegion(1), "23.2.1"));
  EXPECT_TRUE(ParseWithPreprocessorOk(In1995("module generate;\nendmodule\n")));

  // §6.8 owns the report on the instance name, not §23.3.2: an instantiation
  // is recognized by the identifier that follows the module name, so
  // Parser::ParseImplicitTypeOrInst hands `sub` to Parser::ParsePlainVarDecl
  // instead and that demands a semicolon at src/parser/parser_items.cpp:712.
  auto as_instance =
      ParseWithPreprocessor(InNoconfig("module sub;\nendmodule\n"
                                       "module top;\n  sub localparam ();\n"
                                       "endmodule\n"));
  EXPECT_TRUE(ReportedError(as_instance.diags, "expected ';', got token",
                            LineInRegion(4), "6.8"));
}

// The bound from above: this version reserves no more than "1364-2001" does,
// so a word a later list introduces carries no keyword meaning here either.
// `uwire` is the sharpest case, being the sole addition of the very next
// version. Each case is paired with the same source outside the region, which
// is what shows the region and not some unrelated limitation is rejecting it.
TEST(CompilerDirectiveParsing, WordOutsideNoconfigListIsNotAKeyword) {
  // §23.3.2 owns the report: with the word an ordinary identifier the two
  // names read as a module name and an instance name, so
  // Parser::ParseModuleInstList is looking for the port connection list.
  auto as_net =
      ParseWithPreprocessor(InNoconfig("module m;\n  uwire w;\n"
                                       "endmodule\n"));
  EXPECT_TRUE(ReportedError(as_net.diags, "expected '(', got ';'",
                            LineInRegion(2), "23.3.2"));
  EXPECT_TRUE(ParseWithPreprocessorOk("module m;\n  uwire w;\nendmodule\n"));

  // §6.8 owns this one instead: a packed dimension is where the declaration
  // was meant to end, so Parser::ParsePlainVarDecl demands the semicolon at
  // src/parser/parser_items.cpp:712.
  auto as_type =
      ParseWithPreprocessor(InNoconfig("module m;\n"
                                       "  logic [7:0] v;\n"
                                       "endmodule\n"));
  EXPECT_TRUE(ReportedError(as_type.diags, "expected ';', got '['",
                            LineInRegion(2), "6.8"));
  EXPECT_TRUE(
      ParseWithPreprocessorOk("module m;\n  logic [7:0] v;\nendmodule\n"));

  auto as_process =
      ParseWithPreprocessor(InNoconfig("module m;\n"
                                       "  reg r;\n"
                                       "  always_comb r = 1'b0;\n"
                                       "endmodule\n"));
  EXPECT_TRUE(ReportedError(as_process.diags, "expected '(', got '='",
                            LineInRegion(3), "23.3.2"));
}

// Words neither table lists are ordinary identifiers under this version too,
// exactly as they are under the version it is defined from -- the exception
// adds ten names to that group without disturbing it.
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

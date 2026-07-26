#include <cstddef>
#include <iterator>
#include <string>

#include "fixture_parser.h"
#include "helpers_identifier_position_sweep.h"
#include "helpers_included_keyword_parse.h"
#include "helpers_keyword_sweep_skips.h"
#include "helpers_keyword_version.h"
#include "helpers_parser_verify.h"
#include "model_identifier_positions.h"
#include "model_keyword_tables.h"

using namespace delta;

namespace {
// The first included list at this stage: all 102 of Table 22-1 stay reserved,
// so none of them can occupy the identifier slot of a declaration. Sweeping the
// table whole is what makes the inclusion, rather than a handful of its
// entries, the thing being checked.
TEST(CompilerDirectiveParsing,
     SystemVerilog2005ReservesEveryVerilog1995Keyword) {
  ExpectKeywordTableIsReservedAtParse("1800-2005", kSweepTable221AtParse);
}

// The second included list, with the leg that makes it an inclusion. Each of
// Table 22-2's twenty-one entries is rejected here and accepted under
// "1364-1995", where it is not yet a keyword -- so the rejection is this
// version's list doing its work rather than an unrelated parse failure.
TEST(CompilerDirectiveParsing,
     SystemVerilog2005ReservesEveryVerilog2001Keyword) {
  ExpectKeywordTableIsReservedAtParse("1800-2005", kSweepTable222);
}

// The third included list. Its one word cannot name a variable here, names one
// under both lists the version it comes from is built on, and still opens the
// net declaration it exists for -- inclusion is about the keyword role
// surviving, not only about the identifier slot closing.
TEST(CompilerDirectiveParsing, SystemVerilog2005ReservesTheVerilog2005Word) {
  ExpectKeywordTableIsReservedAtParse("1800-2005", kSweepTable223);
  ExpectUwireStillOpensNetDeclarations("1800-2005");
}

// Table 22-4 swept whole in an identifier slot, with the leg that makes each
// entry an addition. The word cannot name a variable here, and under
// "1364-2005" -- the union of everything this version includes -- the very same
// declaration is built and read back off the tree. Any word for which both legs
// hold is reserved by this version_specifier and by nothing it inherits.
TEST(CompilerDirectiveParsing, SystemVerilog2005ReservesEveryWordItAdds) {
  ExpectKeywordTableIsReservedAtParse("1800-2005", kSweepTable224);
}

// The identifier positions a variable declaration does not reach, for the three
// lists this version *includes*. Being on this version's list has to stop a
// word from naming anything at all, not just from naming a variable, so one
// word from each included table is put in turn where a design element, a port,
// an instance, a task, and a named block take their names -- five productions,
// each reached by its own path. Every one is rejected. The accepting
// counterpart is the test below, which runs the same five positions with words
// this version leaves free, so the rejections here cannot be blamed on the
// positions themselves.
//
// Table 22-4 is deliberately absent from the word list. Its position axis is
// carried by AddedWordsNameEntitiesUnderIncludedLists, which runs these same
// five templates plus three more against three added words and asserts this
// same rejection -- so listing an added word here would be a strictly weaker
// copy of what that test already does.
TEST(CompilerDirectiveParsing,
     SystemVerilog2005ReservedWordsFillNoIdentifierPosition) {
  ExpectWordsFillNoIdentifierPosition(
      "1800-2005", {"wire", "generate", "uwire"},
      {"design element", "port", "instance", "task", "named block"});
}

// The same five positions filled by words the four tables do not list, which is
// the accepting side of the bound this version's list sets. Each names its
// entity and the source parses, so the rejections above belong to the reserved
// word list rather than to anything about the positions. Three of the five are
// read back off the tree so the words are observed naming things.
TEST(CompilerDirectiveParsing,
     SystemVerilog2005UnlistedWordsFillEveryIdentifierPosition) {
  ExpectUnlistedWordsNameEveryEntity("1800-2005", {"checker", "let"});
}

// The other side of the addition across the positions an identifier can occupy.
// The sweep above closes the variable-declaration slot for every added word and
// the test above that closes five further positions, but neither shows the
// words free in those positions under the lists this version includes -- the
// accepting leg there is carried by words a *later* standard reserves, which
// says nothing about Table 22-4. So the added words are put in each of eight
// positions under "1364-2005", the union of everything this version includes,
// where they are still ordinary identifiers. Three of the eight -- a function
// name, a gate instance name, and a genvar -- are reached by no other test
// here. Each case is paired with the same source under this version, which
// reserves the word and so admits none of them.
TEST(CompilerDirectiveParsing,
     SystemVerilog2005AddedWordsNameEntitiesUnderIncludedLists) {
  ExpectWordsNameEntitiesUnder("1364-2005", "1800-2005",
                               {"logic", "int", "bit"});

  // Two of those positions read back, so the accepting legs are observed naming
  // things rather than merely parsing.
  auto named_module =
      ParseWithPreprocessor(In2005("module logic;\nendmodule\n"));
  ASSERT_NE(named_module.cu, nullptr);
  ASSERT_EQ(named_module.cu->modules.size(), 1u);
  EXPECT_EQ(named_module.cu->modules[0]->name, "logic");

  auto named_gate =
      ParseWithPreprocessor(In2005("module m (input wire a, output wire y);\n"
                                   "  and int (y, a, a);\n"
                                   "endmodule\n"));
  ASSERT_NE(named_gate.cu, nullptr);
  auto* gate = FindGateByKind(named_gate.cu->modules[0]->items, GateKind::kAnd);
  ASSERT_NE(gate, nullptr);
  EXPECT_EQ(gate->gate_inst_name, "int");
}

// The declaration forms the type test below does not reach. A declaration may
// carry its own initializer, and a port may be declared either in the header or
// in the separate style where the header lists only names and the body supplies
// direction and type. Each is a production of its own, and a word this version
// adds has to type the object in every one of them.
TEST(CompilerDirectiveParsing,
     SystemVerilog2005AddedTypeWordsTypeEveryDeclarationForm) {
  auto with_initializer =
      ParseWithPreprocessor(InSv2005("module m;\n"
                                     "  int   counted = 21;\n"
                                     "  byte  stepped = 8'd1;\n"
                                     "  logic [7:0] held = 8'd0;\n"
                                     "endmodule\n"));
  ASSERT_NE(with_initializer.cu, nullptr);
  EXPECT_FALSE(with_initializer.has_errors);
  const char* kInitialized[] = {"counted", "stepped", "held"};
  for (const char* name : kInitialized) {
    bool found = false;
    for (auto* item : with_initializer.cu->modules[0]->items) {
      if (item->kind != ModuleItemKind::kVarDecl || item->name != name)
        continue;
      found = true;
      // The declaration brings its own value rather than leaning on a separate
      // procedural assignment, which is what makes this a form of its own.
      EXPECT_NE(item->init_expr, nullptr) << name;
    }
    EXPECT_TRUE(found) << name;
  }

  auto ansi_ports = ParseWithPreprocessor(
      InSv2005("module ch (input logic [7:0] a, input byte b, output int y);\n"
               "  assign y = a + b;\n"
               "endmodule\n"));
  ASSERT_NE(ansi_ports.cu, nullptr);
  EXPECT_FALSE(ansi_ports.has_errors);
  auto* ch = ansi_ports.cu->modules[0];
  ASSERT_EQ(ch->ports.size(), 3u);
  EXPECT_EQ(ch->ports[0].data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(ch->ports[1].data_type.kind, DataTypeKind::kByte);
  EXPECT_EQ(ch->ports[2].data_type.kind, DataTypeKind::kInt);

  auto non_ansi =
      ParseWithPreprocessor(InSv2005("module ch (a, y);\n"
                                     "  input  [7:0] a;\n"
                                     "  output [7:0] y;\n"
                                     "  logic  [7:0] y;\n"
                                     "  always_comb y = a + a;\n"
                                     "endmodule\n"));
  ASSERT_NE(non_ansi.cu, nullptr);
  EXPECT_FALSE(non_ansi.has_errors);
  auto* body_typed = non_ansi.cu->modules[0];
  ASSERT_EQ(body_typed->ports.size(), 2u);
  EXPECT_EQ(body_typed->ports[1].name, "y");
  bool typed_in_body = false;
  for (auto* item : body_typed->items) {
    if (item->kind == ModuleItemKind::kVarDecl && item->name == "y") {
      EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
      typed_in_body = true;
    }
  }
  EXPECT_TRUE(typed_in_body);

  // None of the three forms can be written under the union of everything this
  // version includes, where the words introduce nothing.
  EXPECT_FALSE(
      ParseWithPreprocessorOk(In2005("module m;\n  int counted = 21;\n"
                                     "endmodule\n")));
  EXPECT_FALSE(ParseWithPreprocessorOk(
      In2005("module ch (input logic [7:0] a, output int y);\n"
             "  assign y = a;\n"
             "endmodule\n")));
  EXPECT_FALSE(
      ParseWithPreprocessorOk(In2005("module ch (a, y);\n"
                                     "  input  [7:0] a;\n"
                                     "  output [7:0] y;\n"
                                     "  logic  [7:0] y;\n"
                                     "endmodule\n")));
}

// The keyword roles the additions exist for, starting with the data types.
// Reserving a word is only half of what the version_specifier buys; the other
// half is that the word now introduces something, and each of these opens a
// declaration whose type is read back off the tree. Under "1364-2005", where
// none of them is reserved, the same source is not a set of declarations at
// all.
TEST(CompilerDirectiveParsing,
     SystemVerilog2005AddedTypeWordsOpenDeclarations) {
  const std::string kSrc =
      "module m;\n"
      "  logic     [7:0] a;\n"
      "  bit       [7:0] b;\n"
      "  byte            c;\n"
      "  shortint        d;\n"
      "  int             e;\n"
      "  longint         f;\n"
      "  shortreal       g;\n"
      "  string          h;\n"
      "  chandle         i;\n"
      "  var logic [7:0] j;\n"
      "  const int       k = 5;\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(InSv2005(kSrc));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);

  struct TypedDecl {
    const char* name;
    DataTypeKind kind;
  };
  const TypedDecl kDecls[] = {
      {"a", DataTypeKind::kLogic},     {"b", DataTypeKind::kBit},
      {"c", DataTypeKind::kByte},      {"d", DataTypeKind::kShortint},
      {"e", DataTypeKind::kInt},       {"f", DataTypeKind::kLongint},
      {"g", DataTypeKind::kShortreal}, {"h", DataTypeKind::kString},
      {"i", DataTypeKind::kChandle},   {"j", DataTypeKind::kLogic},
      {"k", DataTypeKind::kInt},
  };
  for (const auto& d : kDecls) {
    bool found = false;
    for (auto* item : r.cu->modules[0]->items) {
      if (item->kind != ModuleItemKind::kVarDecl || item->name != d.name)
        continue;
      found = true;
      EXPECT_EQ(item->data_type.kind, d.kind) << d.name;
    }
    EXPECT_TRUE(found) << d.name;
  }

  EXPECT_FALSE(ParseWithPreprocessorOk(In2005(kSrc)));
}

// The aggregate and user-defined type words, which reach the parser by a path
// of their own: `typedef` introduces a name for a type, `enum`, `struct`,
// `union` and `packed` build the types it names, and `type` appears as a
// parameter kind. The declared names are read back, and the same source under
// the union of everything this version includes is rejected.
TEST(CompilerDirectiveParsing,
     SystemVerilog2005AddedAggregateWordsOpenDeclarations) {
  const std::string kSrc =
      "module m;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  typedef enum {IDLE, BUSY} state_t;\n"
      "  typedef struct packed { logic [3:0] hi; logic [3:0] lo; } pair_t;\n"
      "  typedef union packed { logic [7:0] whole; pair_t split; } view_t;\n"
      "  byte_t  v;\n"
      "  state_t s;\n"
      "  pair_t  p;\n"
      "  view_t  u;\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(InSv2005(kSrc));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto& items = r.cu->modules[0]->items;
  for (const char* name : {"byte_t", "state_t", "pair_t", "view_t"}) {
    EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kTypedef, name))
        << name;
  }
  for (const char* name : {"v", "s", "p", "u"}) {
    bool found = false;
    for (auto* item : items) {
      if (item->kind != ModuleItemKind::kVarDecl || item->name != name)
        continue;
      found = true;
      EXPECT_EQ(item->data_type.kind, DataTypeKind::kNamed) << name;
    }
    EXPECT_TRUE(found) << name;
  }

  EXPECT_FALSE(ParseWithPreprocessorOk(In2005(kSrc)));
}

// The words that open a process. Each of the three inferred always forms and
// the final block is a module item of its own kind, so the tree says outright
// which word opened which -- something no identifier-slot rejection could show.
TEST(CompilerDirectiveParsing, SystemVerilog2005AddedProcessWordsOpenBlocks) {
  const std::string kSrc =
      "module m (input logic clk, input logic d, output logic q);\n"
      "  logic combo;\n"
      "  logic latched;\n"
      "  always_comb  combo = d;\n"
      "  always_ff  @(posedge clk) q <= combo;\n"
      "  always_latch if (clk) latched = d;\n"
      "  final begin end\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(InSv2005(kSrc));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto& items = r.cu->modules[0]->items;
  EXPECT_NE(FindItemByKind(items, ModuleItemKind::kAlwaysCombBlock), nullptr);
  EXPECT_NE(FindItemByKind(items, ModuleItemKind::kAlwaysFFBlock), nullptr);
  EXPECT_NE(FindItemByKind(items, ModuleItemKind::kAlwaysLatchBlock), nullptr);
  EXPECT_NE(FindItemByKind(items, ModuleItemKind::kFinalBlock), nullptr);

  EXPECT_FALSE(ParseWithPreprocessorOk(In2005(kSrc)));
}

// The words that open a statement rather than a declaration or a process. The
// loop-control and return statements, the do-while and foreach loops, and the
// case qualifiers are all reached through a procedural block, which is a path
// of its own. The statement kinds are read back off the initial block's body.
TEST(CompilerDirectiveParsing,
     SystemVerilog2005AddedStatementWordsOpenStatements) {
  const std::string kSrc =
      "module m;\n"
      "  int  arr [0:3];\n"
      "  int  i;\n"
      "  int  total;\n"
      "  logic [1:0] sel;\n"
      "  function int twice(input int n);\n"
      "    return n + n;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    do total = total + 1; while (total < 2);\n"
      "    foreach (arr[j]) total = total + 1;\n"
      "    for (i = 0; i < 4; i = i + 1) begin\n"
      "      if (i == 1) continue;\n"
      "      if (i == 3) break;\n"
      "    end\n"
      "    unique case (sel) 2'b01: total = 1; default: total = 0; endcase\n"
      "    priority case (sel) 2'b01: total = 2; default: total = 0; endcase\n"
      "    if (sel inside {2'b01, 2'b10}) total = twice(3);\n"
      "  end\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(InSv2005(kSrc));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto* init =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kInitialBlock);
  ASSERT_NE(init, nullptr);
  ASSERT_NE(init->body, nullptr);

  auto has_kind = [](Stmt* block, StmtKind kind) {
    for (auto* s : block->stmts) {
      if (s != nullptr && s->kind == kind) return true;
    }
    return false;
  };
  EXPECT_TRUE(has_kind(init->body, StmtKind::kDoWhile));
  EXPECT_TRUE(has_kind(init->body, StmtKind::kForeach));

  auto* fn =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kFunctionDecl);
  ASSERT_NE(fn, nullptr);
  EXPECT_EQ(fn->name, "twice");

  EXPECT_FALSE(ParseWithPreprocessorOk(In2005(kSrc)));
}

// The words that open a design element, which is the outermost syntactic
// position any of the additions reaches. An interface with a modport, a package
// with a constant that is then imported, a program, and a class hierarchy each
// land in their own list on the compilation unit, so what opened them is read
// back rather than inferred from the source parsing.
TEST(CompilerDirectiveParsing,
     SystemVerilog2005AddedDesignElementWordsOpenElements) {
  const std::string kSrc =
      "package pkg;\n"
      "  localparam int WIDTH = 8;\n"
      "endpackage\n"
      "interface ifc;\n"
      "  logic [7:0] data;\n"
      "  modport source (output data);\n"
      "endinterface\n"
      "program prg;\n"
      "  initial begin end\n"
      "endprogram\n"
      "class base;\n"
      "  int v;\n"
      "  function new(); v = 1; endfunction\n"
      "endclass\n"
      "class derived extends base;\n"
      "  virtual function void bump(); this.v = super.v + 1; endfunction\n"
      "endclass\n"
      "module m;\n"
      "  import pkg::*;\n"
      "  logic [7:0] w;\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(InSv2005(kSrc));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->name, "ifc");
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "prg");
  ASSERT_EQ(r.cu->classes.size(), 2u);
  EXPECT_EQ(r.cu->classes[0]->name, "base");
  EXPECT_EQ(r.cu->classes[1]->name, "derived");

  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_NE(
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kImportDecl),
      nullptr);

  EXPECT_FALSE(ParseWithPreprocessorOk(In2005(kSrc)));
}

// The verification vocabulary, which is the part of Table 22-4 with no Verilog
// ancestor at all: an immediate assertion, a named property and sequence, a
// cover statement, a covergroup with a coverpoint and its bins, a clocking
// block, and the fork-join variants. Each lands as its own module item.
TEST(CompilerDirectiveParsing,
     SystemVerilog2005AddedVerificationWordsOpenConstructs) {
  const std::string kSrc =
      "module m (input logic clk, input logic req, input logic ack);\n"
      "  logic [7:0] count;\n"
      "  property p_handshake;\n"
      "    @(posedge clk) req |-> ack;\n"
      "  endproperty\n"
      "  sequence s_pulse;\n"
      "    @(posedge clk) req;\n"
      "  endsequence\n"
      "  clocking cb @(posedge clk);\n"
      "    input req;\n"
      "  endclocking\n"
      "  covergroup cg @(posedge clk);\n"
      "    cp_count: coverpoint count {\n"
      "      bins low  = {0};\n"
      "      bins high = {255};\n"
      "    }\n"
      "  endgroup\n"
      "  initial begin\n"
      "    assert (count == 8'd0);\n"
      "    fork\n"
      "      count = 8'd1;\n"
      "    join_none\n"
      "    fork\n"
      "      count = 8'd2;\n"
      "    join_any\n"
      "  end\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(InSv2005(kSrc));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto& items = r.cu->modules[0]->items;
  EXPECT_TRUE(
      HasItemKindNamed(items, ModuleItemKind::kPropertyDecl, "p_handshake"));
  EXPECT_TRUE(
      HasItemKindNamed(items, ModuleItemKind::kSequenceDecl, "s_pulse"));
  EXPECT_NE(FindItemByKind(items, ModuleItemKind::kClockingBlock), nullptr);
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kCovergroupDecl, "cg"));

  EXPECT_FALSE(ParseWithPreprocessorOk(In2005(kSrc)));
}

// Table 22-1 in its keyword role under this version: inclusion is not only
// about what a word may no longer name. The gate primitives build structure,
// the resolved net types and drive strengths are written out, and the
// procedural statements build control flow -- all under a region opened for
// this version_specifier.
TEST(CompilerDirectiveParsing,
     SystemVerilog2005IncludedVerilog1995WordsStillWork) {
  ExpectTable221ConstructsParse("1800-2005");
}

// Including Table 22-2 means including the ten words a configuration is written
// with, which is the sharpest thing that list contributes: seven of them appear
// here and the declaration is built. Under "1364-1995", the first of the three
// lists this version includes, none of the words is reserved and the construct
// cannot be written -- so the configuration exists here because of the second
// inclusion and not by default.
TEST(CompilerDirectiveParsing, SystemVerilog2005IncludesTheConfigurationWords) {
  ExpectConfigurationWordsParse("1800-2005");
}

// The rest of Table 22-2 in its keyword role. `localparam` declares a constant,
// `genvar`/`generate`/`endgenerate` build a loop generate construct,
// `automatic` qualifies a subroutine, `signed` and `unsigned` qualify
// declarations, and the four pulse-control words are specify items -- each the
// construct its word exists to open, all still available under this version.
TEST(CompilerDirectiveParsing,
     SystemVerilog2005IncludedVerilog2001WordsStillWork) {
  ExpectTable222ConstructsParse("1800-2005");
}

// The negative the four tables imply, at the stage where it shows: a word none
// of them lists is an ordinary identifier under this version, so it names
// things freely and opens nothing. Both halves are here -- the same word naming
// a declaration and failing to be a data type -- because either one alone would
// leave the other unchecked.
TEST(CompilerDirectiveParsing,
     SystemVerilog2005LeavesUnlistedWordsAsIdentifiers) {
  // None of these opens a design element, so putting one at the head of a line
  // leaves the region machinery -- which tracks design elements by a line's
  // first word, without regard to the list in force -- out of the picture, and
  // the only thing that can reject the source is the word not being a type.
  const char* kUnlisted[] = {"until", "let", "global", "nettype", "soft"};
  for (const char* word : kUnlisted) {
    auto r = ParseWithPreprocessor(InSv2005(VarDecl(word)));
    ASSERT_NE(r.cu, nullptr) << word;
    EXPECT_FALSE(r.has_errors) << word;
    ASSERT_EQ(r.cu->modules.size(), 1u) << word;
    EXPECT_TRUE(HasItemKindNamed(r.cu->modules[0]->items,
                                 ModuleItemKind::kVarDecl, word))
        << word;

    std::string as_type =
        std::string("module m;\n  ") + word + " [7:0] v;\nendmodule\n";
    EXPECT_FALSE(ParseWithPreprocessorOk(InSv2005(as_type)))
        << word << " is not a data type under this version";
  }
}

}  // namespace

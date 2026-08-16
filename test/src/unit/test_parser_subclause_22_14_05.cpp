#include <cstddef>
#include <iterator>
#include <string>

#include "fixture_parser.h"
#include "helpers_identifier_position_sweep.h"
#include "helpers_included_keyword_parse.h"
#include "helpers_keyword_version.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "model_identifier_positions.h"
#include "model_keyword_tables.h"

using namespace delta;

namespace {
// The first included list at this stage: all 102 of Table 22-1 stay reserved,
// so none of them can occupy the identifier slot of a declaration. Sweeping the
// table whole is what makes the inclusion, rather than a handful of its
// entries, the thing being checked.
TEST(CompilerDirectiveParsing, Verilog2005ReservesEveryVerilog1995Keyword) {
  EXPECT_EQ(std::size(kTable221), 102u);
  for (const char* word : kTable221) {
    // §6.8 owns the report: VarDecl heads its declaration with `reg`, so the
    // word stands where Parser::ParseVarDeclList reads a variable's name. The
    // expected message is built from the word, so each entry of the table is
    // covered by a report naming it rather than by one sentence they share.
    auto r = ParseWithPreprocessor(In2005(VarDecl(word)));
    EXPECT_TRUE(ReportedError(
        r.diags, std::string("expected identifier, got '") + word + "'",
        LineInRegion(2), "6.8"))
        << word << " is included from Table 22-1 and stays reserved";
  }
}

// The second included list, with the leg that makes it an inclusion. Each of
// Table 22-2's twenty-one entries is rejected here and accepted under
// "1364-1995", where it is not yet a keyword -- so the rejection is this
// version's list doing its work rather than an unrelated parse failure.
TEST(CompilerDirectiveParsing, Verilog2005ReservesEveryVerilog2001Keyword) {
  EXPECT_EQ(std::size(kTable222Words), 21u);
  for (const char* word : kTable222Words) {
    auto r = ParseWithPreprocessor(In2005(VarDecl(word)));
    EXPECT_TRUE(ReportedError(
        r.diags, std::string("expected identifier, got '") + word + "'",
        LineInRegion(2), "6.8"))
        << word << " is included from Table 22-2 and is reserved here";
    EXPECT_TRUE(ParseWithPreprocessorOk(In1995(VarDecl(word))))
        << word << " is an addition of the later of the two included lists";
  }
}

// The identifier positions a variable declaration does not reach. Being on this
// version's list has to stop a word from naming anything at all, not just from
// naming a variable, so words drawn from each of the three tables are put in
// turn where a design element, a port, an instance, a task, and a named block
// take their names -- five productions, each reached by its own path. Every one
// is rejected. The accepting counterpart is the test below, which runs the same
// five positions with a word this version leaves free, so the rejections here
// cannot be blamed on the positions themselves.
TEST(CompilerDirectiveParsing,
     Verilog2005ReservedWordsFillNoIdentifierPosition) {
  ExpectWordsFillNoIdentifierPosition(
      "1364-2005", {"wire", "generate", "uwire"},
      {"design element", "port", "instance", "task", "named block"});
}

// The same five positions filled by words the three tables do not list, which
// is the accepting side of the bound this version's list sets. Each names its
// entity and the source parses, so the rejections above belong to the reserved
// word list rather than to anything about the positions. Three of the five
// are read back off the tree so the words are observed naming things.
TEST(CompilerDirectiveParsing,
     Verilog2005UnlistedWordsFillEveryIdentifierPosition) {
  ExpectUnlistedWordsNameEveryEntity("1364-2005", {"logic", "bit"});
}

// Table 22-3, and what makes it an addition rather than an inheritance: the one
// word it holds cannot name a variable here, and names one under both of the
// lists this version includes. The accepting legs are read back off the parsed
// tree, so the word is observed naming something rather than merely getting
// past the lexer.
TEST(CompilerDirectiveParsing, Verilog2005ReservesTheWordItAddsItself) {
  ASSERT_EQ(std::size(kTable223), 1u);
  const char* added = kTable223[0];

  auto here = ParseWithPreprocessor(In2005(VarDecl(added)));
  EXPECT_TRUE(ReportedError(
      here.diags, std::string("expected identifier, got '") + added + "'",
      LineInRegion(2), "6.8"));

  for (const auto& earlier : {In2001(VarDecl(added)), In1995(VarDecl(added))}) {
    auto r = ParseWithPreprocessor(earlier);
    ASSERT_NE(r.cu, nullptr);
    EXPECT_FALSE(r.has_errors);
    ASSERT_EQ(r.cu->modules.size(), 1u);
    EXPECT_TRUE(HasItemKindNamed(r.cu->modules[0]->items,
                                 ModuleItemKind::kVarDecl, added));
  }
}

// The added word in its keyword role, which is where the addition has its
// point: it opens a net declaration. Every form the declaration takes is here
// -- a scalar, a vector, a signed vector, and a port -- because each reaches
// the parser by its own path, and each is read back as the net type the word
// names. The same source under the later of the two included lists cannot be
// written at all, since there the word is just an identifier.
TEST(CompilerDirectiveParsing, Verilog2005AddedWordOpensANetDeclaration) {
  auto r = ParseWithPreprocessor(
      In2005("module m (input wire [7:0] a, output uwire [7:0] y);\n"
             "  uwire        scalar_net;\n"
             "  uwire [3:0]  vector_net;\n"
             "  uwire signed [7:0] signed_net;\n"
             "  assign y = a;\n"
             "endmodule\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);

  auto* m = r.cu->modules[0];
  ASSERT_EQ(m->ports.size(), 2u);
  EXPECT_EQ(m->ports[1].name, "y");
  EXPECT_EQ(m->ports[1].direction, Direction::kOutput);
  EXPECT_EQ(m->ports[1].data_type.kind, DataTypeKind::kUwire);

  const char* const kNets[] = {"scalar_net", "vector_net", "signed_net"};
  for (const char* name : kNets) {
    bool found = false;
    for (auto* item : m->items) {
      if (item->kind != ModuleItemKind::kNetDecl || item->name != name)
        continue;
      found = true;
      EXPECT_EQ(item->data_type.kind, DataTypeKind::kUwire) << name;
    }
    EXPECT_TRUE(found) << name;
  }

  bool signed_seen = false;
  for (auto* item : m->items) {
    if (item->kind == ModuleItemKind::kNetDecl && item->name == "signed_net") {
      EXPECT_TRUE(item->data_type.is_signed);
      signed_seen = true;
    }
  }
  EXPECT_TRUE(signed_seen);

  // Under the list this version extends the same declarations are not
  // declarations at all. §23.3.2 owns the report, not §6.7: with the word an
  // ordinary identifier the two names read as a module name and an instance
  // name, so Parser::ParseModuleInstList is looking for the port connection
  // list when it reaches the semicolon.
  auto earlier =
      ParseWithPreprocessor(In2001("module m;\n"
                                   "  uwire scalar_net;\n"
                                   "endmodule\n"));
  EXPECT_TRUE(ReportedError(earlier.diags, "expected '(', got ';'",
                            LineInRegion(2), "23.3.2"));
}

// The declaration forms the test above does not reach. A net declaration may
// carry its own assignment, and a port may be declared in the separate style
// where the header lists only names and the body gives each one its direction
// and its type -- both are productions of their own, and the added word has to
// open the net in each. The paired legs reject the same sources under the later
// of the two included lists, where the word introduces nothing.
TEST(CompilerDirectiveParsing, Verilog2005AddedWordTypesEveryDeclarationForm) {
  auto with_assignment =
      ParseWithPreprocessor(In2005("module m;\n"
                                   "  reg   [7:0] src;\n"
                                   "  uwire [7:0] bus = src + 8'd1;\n"
                                   "endmodule\n"));
  ASSERT_NE(with_assignment.cu, nullptr);
  EXPECT_FALSE(with_assignment.has_errors);
  bool bus_seen = false;
  for (auto* item : with_assignment.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kNetDecl || item->name != "bus") continue;
    bus_seen = true;
    EXPECT_EQ(item->data_type.kind, DataTypeKind::kUwire);
    // The declaration carries its driver rather than leaning on a separate
    // continuous assignment, which is what makes this a form of its own.
    EXPECT_NE(item->init_expr, nullptr);
  }
  EXPECT_TRUE(bus_seen);

  auto non_ansi =
      ParseWithPreprocessor(In2005("module ch (a, y);\n"
                                   "  input  [7:0] a;\n"
                                   "  output [7:0] y;\n"
                                   "  uwire  [7:0] y;\n"
                                   "  assign y = a;\n"
                                   "endmodule\n"));
  ASSERT_NE(non_ansi.cu, nullptr);
  EXPECT_FALSE(non_ansi.has_errors);
  auto* ch = non_ansi.cu->modules[0];
  ASSERT_EQ(ch->ports.size(), 2u);
  EXPECT_EQ(ch->ports[1].name, "y");
  bool typed_in_body = false;
  for (auto* item : ch->items) {
    if (item->kind == ModuleItemKind::kNetDecl && item->name == "y") {
      EXPECT_EQ(item->data_type.kind, DataTypeKind::kUwire);
      typed_in_body = true;
    }
  }
  EXPECT_TRUE(typed_in_body);

  // §6.8 owns both reports. A packed dimension is where the declaration was
  // meant to end, so with the word an ordinary identifier
  // Parser::ParsePlainVarDecl in src/parser/parser_items.cpp reads it as a
  // variable of an implicit type and demands the semicolon.
  auto assigned =
      ParseWithPreprocessor(In2001("module m;\n"
                                   "  reg   [7:0] src;\n"
                                   "  uwire [7:0] bus = src + 8'd1;\n"
                                   "endmodule\n"));
  EXPECT_TRUE(ReportedError(assigned.diags, "expected ';', got '['",
                            LineInRegion(3), "6.8"));

  auto in_body =
      ParseWithPreprocessor(In2001("module ch (a, y);\n"
                                   "  input  [7:0] a;\n"
                                   "  output [7:0] y;\n"
                                   "  uwire  [7:0] y;\n"
                                   "endmodule\n"));
  EXPECT_TRUE(ReportedError(in_body.diags, "expected ';', got '['",
                            LineInRegion(4), "6.8"));
}

// The other side of the addition across the positions an identifier can occupy.
// A declaration is only the most obvious one, so the word this version adds is
// put in each of the rest -- naming a design element, a port, an instance, a
// task, a function, a gate instance, and a genvar -- under the later of the two
// lists this version includes, where it is still an ordinary identifier. Each
// case is paired with the same source under this version, which reserves the
// word and so admits none of them.
TEST(CompilerDirectiveParsing, Verilog2005AddedWordNamesEntitiesUnderEarlier) {
  ExpectWordsNameEntitiesUnder("1364-2001", "1364-2005", {"uwire"},
                               {"design element", "port", "instance", "task",
                                "function", "gate instance", "genvar"});

  // Two of those positions read back, so the accepting legs are observed
  // naming things rather than merely parsing.
  auto named_module = ParseWithPreprocessor(
      In2001(AtPosition(kIdentifierPositions[0], "uwire")));
  ASSERT_NE(named_module.cu, nullptr);
  ASSERT_EQ(named_module.cu->modules.size(), 1u);
  EXPECT_EQ(named_module.cu->modules[0]->name, "uwire");

  auto named_instance = ParseWithPreprocessor(
      In2001(AtPosition(kIdentifierPositions[2], "uwire")));
  ASSERT_NE(named_instance.cu, nullptr);
  ASSERT_EQ(named_instance.cu->modules.size(), 2u);
  auto* inst = FindItemByKind(named_instance.cu->modules[1]->items,
                              ModuleItemKind::kModuleInst);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->inst_name, "uwire");
}

// Including Table 22-2 whole means including the ten words a configuration is
// written with, which is the sharpest thing that list contributes: seven of
// them appear here and the declaration is built. Under "1364-1995", the other
// list this version includes, none of the words is reserved and the construct
// cannot be written -- so the configuration exists here because of the second
// inclusion and not by default.
TEST(CompilerDirectiveParsing, Verilog2005IncludesTheConfigurationWords) {
  ExpectConfigurationWordsParse("1364-2005");
}

// The rest of Table 22-2 in its keyword role rather than in an identifier slot.
// `localparam` declares a constant, `genvar`/`generate`/`endgenerate` build a
// loop generate construct, `automatic` qualifies a subroutine, `signed` and
// `unsigned` qualify declarations, and the four pulse-control words are specify
// items -- each the construct its word exists to open.
TEST(CompilerDirectiveParsing,
     Verilog2005IncludedAdditionsOpenTheirConstructs) {
  ExpectTable222ConstructsParse("1364-2005");
}

// Table 22-1 in its keyword role too: inclusion is not only about what a word
// may no longer name. The gate primitives build structure, the resolved net
// types and drive strengths are written out, and the procedural statements
// build control flow -- all of it under a region opened for this version.
TEST(CompilerDirectiveParsing, Verilog2005IncludedVerilog1995WordsStillWork) {
  ExpectTable221ConstructsParse("1364-2005");
}

// The negative the three tables imply, at the stage where it shows: a word none
// of them lists is an ordinary identifier under this version, so it names
// things freely and opens nothing. Both halves are here -- the same word naming
// a declaration and failing to be a data type -- because either one alone would
// leave the other unchecked.
TEST(CompilerDirectiveParsing, Verilog2005LeavesUnlistedWordsAsIdentifiers) {
  const char* const kUnlisted[] = {"logic", "interface", "bit", "byte", "int"};
  for (const char* word : kUnlisted) {
    auto r = ParseWithPreprocessor(In2005(VarDecl(word)));
    ASSERT_NE(r.cu, nullptr) << word;
    EXPECT_FALSE(r.has_errors) << word;
    ASSERT_EQ(r.cu->modules.size(), 1u) << word;
    EXPECT_TRUE(HasItemKindNamed(r.cu->modules[0]->items,
                                 ModuleItemKind::kVarDecl, word))
        << word;

    std::string as_type =
        std::string("module m;\n  ") + word + " [7:0] v;\nendmodule\n";
    // §6.8 owns the report: the word is an ordinary identifier here, so
    // Parser::ParsePlainVarDecl reads it as a variable of an implicit type and
    // the packed dimension is where it expected the declaration to end.
    auto typed = ParseWithPreprocessor(In2005(as_type));
    EXPECT_TRUE(ReportedError(typed.diags, "expected ';', got '['",
                              LineInRegion(2), "6.8"))
        << word << " is not a data type under this version";
  }
}

}  // namespace

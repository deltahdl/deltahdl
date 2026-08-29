#pragma once

#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string>
#include <string_view>

#include "fixture_parser.h"
#include "helpers_keyword_version.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "model_identifier_positions.h"

using namespace delta;

// Sweeps over the identifier positions of model_identifier_positions.h, for a
// test whose subject is what a `begin_keywords version_specifier reserves.
// Both sweeps take the positions to cover as a list of names; an empty list
// covers every position.

// The report a word the version in force reserves draws in one position, and
// the line of that position's own template the report stands at. A sweep that
// asserted only that something was reported would hold when a different rule
// fired and hold when the source never reached the position at all, so each
// position is answered for by the report its own production emits.
struct PositionReport {
  const char* message;
  uint32_t body_line;
  const char* subclause;
};

// Which report each position of kIdentifierPositions draws, traced through the
// parser. Five of the eight put the word where an identifier is demanded and
// draw "expected identifier, got " from the Expect or ExpectIdentifier call
// that reads the name: Parser::ParseModuleDecl in src/parser/parser.cpp
// under §23.2.1, Parser::ParsePortDecl in src/parser/parser_port.cpp under
// §23.2.2.2, Parser::ParseTaskDecl in src/parser/parser_declaration.cpp
// under §13.3, Parser::ParseFuncName in src/parser/parser_declaration.cpp
// under §13.4, Parser::ParseGenvarDecl in src/parser/parser.cpp under
// §27.4, and Parser::ParseBlockStmt in src/parser/parser_stmt.cpp under
// §9.3.4. The tail of that sentence is left off, because a port whose word is
// itself a data type -- "input wire logic" -- is read as the type and the
// report then stands at the comma rather than at the word.
//
// The other two are reached by no identifier slot at all. A gate instance name
// is optional, so ParseGateInstanceTail in src/parser/parser_toplevel.cpp,
// reached from the call in Parser::ParseOneGateInstance in that same file, is
// told there is no identifier, takes the instance to be unnamed and demands
// the terminal list under §28.3.6. A module instantiation is recognized by the
// identifier that follows the module name, so Parser::ParseImplicitTypeOrInst
// hands "ch" to Parser::ParsePlainVarDecl in src/parser/parser_items.cpp
// instead, which reads it as a variable declaration of an implicit type and
// demands the semicolon under §6.8.
inline PositionReport ReportForPosition(const IdentifierPosition& p) {
  const std::string_view kWhat(p.what);
  if (kWhat == "design element") {
    return {"expected identifier, got ", 1, "23.2.1"};
  }
  if (kWhat == "port") return {"expected identifier, got ", 1, "23.2.2.2"};
  if (kWhat == "instance") return {"expected ';', got ", 6, "6.8"};
  if (kWhat == "task") return {"expected identifier, got ", 3, "13.3"};
  if (kWhat == "function") return {"expected identifier, got ", 3, "13.4"};
  if (kWhat == "gate instance") return {"expected '(', got ", 2, "28.3.6"};
  if (kWhat == "genvar") return {"expected identifier, got ", 2, "27.4"};
  if (kWhat == "named block") return {"expected identifier, got ", 3, "9.3.4"};
  ADD_FAILURE() << p.what << " has no report recorded here";
  return {"", 0, ""};
}

// Every word of `words` put into each covered position and rejected under
// `spec`. A word the specifier reserves cannot name anything, so no position
// admits it.
inline void ExpectWordsFillNoIdentifierPosition(
    const char* spec, std::initializer_list<const char*> words,
    std::initializer_list<std::string_view> positions = {}) {
  for (const auto& p : kIdentifierPositions) {
    if (positions.size() != 0 && !PositionIsOneOf(p, positions)) continue;
    const PositionReport kRep = ReportForPosition(p);
    for (const char* word : words) {
      // Every message here stops before the token the report names, for the
      // reason given above ReportForPosition: a word that is itself a data
      // type is read as the type in some of these positions, and the report
      // then stands at the punctuation that follows rather than at the word.
      // So the word under test is told apart by the failure message rather
      // than by the report.
      auto r = ParseWithPreprocessor(In(spec, AtPosition(p, word)));
      EXPECT_TRUE(ReportedError(r.diags, kRep.message,
                                LineInRegion(kRep.body_line), kRep.subclause))
          << word << " cannot name a " << p.what << " under this version";
    }
  }
}

// The accepting counterpart, which is what keeps the rejections above from
// being blamed on the positions themselves: the same sources under `earlier`,
// a specifier whose list leaves these words free, are accepted. Pairing the
// two legs per position is the whole claim -- the word is reserved *here* and
// an ordinary identifier *there*.
inline void ExpectWordsNameEntitiesUnder(
    const char* earlier, const char* spec,
    std::initializer_list<const char*> words,
    std::initializer_list<std::string_view> positions = {}) {
  for (const auto& p : kIdentifierPositions) {
    if (positions.size() != 0 && !PositionIsOneOf(p, positions)) continue;
    const PositionReport kRep = ReportForPosition(p);
    for (const char* word : words) {
      std::string src = AtPosition(p, word);
      EXPECT_TRUE(ParseWithPreprocessorOk(In(earlier, src)))
          << p.what << ": everything this version includes leaves " << word
          << " free";
      auto r = ParseWithPreprocessor(In(spec, src));
      EXPECT_TRUE(ReportedError(r.diags, kRep.message,
                                LineInRegion(kRep.body_line), kRep.subclause))
          << p.what << ": this version reserves " << word;
    }
  }
}

// Every word of `words` accepted in each of five identifier positions under
// `spec` -- design element, port, instance, task and named block -- with three
// of the five read back off the parsed tree.
//
// This is the accepting side of the bound a version's reserved word list sets:
// a word the list does not hold names each of these entities and the source
// parses, so a rejection recorded for a listed word belongs to the list rather
// than to anything about the position. Reading the name back off the tree is
// what shows the word named the entity rather than merely getting past the
// parser.
inline void ExpectUnlistedWordsNameEveryEntity(
    const char* spec, std::initializer_list<const char*> words) {
  for (const char* word : words) {
    std::string as_module = std::string("module ") + word + ";\nendmodule\n";
    auto named_module = ParseWithPreprocessor(In(spec, as_module));
    ASSERT_NE(named_module.cu, nullptr) << word;
    EXPECT_FALSE(named_module.has_errors) << word;
    ASSERT_EQ(named_module.cu->modules.size(), 1u) << word;
    EXPECT_EQ(named_module.cu->modules[0]->name, word);

    std::string as_port = std::string("module m (input wire ") + word +
                          ", output wire y);\n  assign y = " + word +
                          ";\nendmodule\n";
    auto named_port = ParseWithPreprocessor(In(spec, as_port));
    ASSERT_NE(named_port.cu, nullptr) << word;
    EXPECT_FALSE(named_port.has_errors) << word;
    ASSERT_EQ(named_port.cu->modules[0]->ports.size(), 2u) << word;
    EXPECT_EQ(named_port.cu->modules[0]->ports[0].name, word);

    std::string as_instance = std::string(
                                  "module ch (input wire a, output wire y);\n"
                                  "  assign y = a;\n"
                                  "endmodule\n"
                                  "module top;\n"
                                  "  wire a, b;\n"
                                  "  ch ") +
                              word + " (.a(a), .y(b));\nendmodule\n";
    auto named_instance = ParseWithPreprocessor(In(spec, as_instance));
    ASSERT_NE(named_instance.cu, nullptr) << word;
    EXPECT_FALSE(named_instance.has_errors) << word;
    ASSERT_EQ(named_instance.cu->modules.size(), 2u) << word;
    auto* inst = FindItemByKind(named_instance.cu->modules[1]->items,
                                ModuleItemKind::kModuleInst);
    ASSERT_NE(inst, nullptr) << word;
    EXPECT_EQ(inst->inst_name, word);

    std::string as_task = std::string("module m;\n  reg [7:0] r;\n  task ") +
                          word + "; r = 8'd1; endtask\n  initial begin : blk " +
                          word + "; end\nendmodule\n";
    EXPECT_TRUE(ParseWithPreprocessorOk(In(spec, as_task))) << word;

    std::string as_block =
        std::string("module m;\n  reg [7:0] r;\n  initial begin : ") + word +
        " r = 8'd1; end\nendmodule\n";
    EXPECT_TRUE(ParseWithPreprocessorOk(In(spec, as_block))) << word;
  }
}

#pragma once

#include <gtest/gtest.h>

#include <initializer_list>
#include <string>
#include <string_view>

#include "fixture_parser.h"
#include "helpers_keyword_version.h"
#include "helpers_parser_verify.h"
#include "model_identifier_positions.h"

using namespace delta;

// Sweeps over the identifier positions of model_identifier_positions.h, for a
// test whose subject is what a `begin_keywords version_specifier reserves.
// Both sweeps take the positions to cover as a list of names; an empty list
// covers every position.

// Every word of `words` put into each covered position and rejected under
// `spec`. A word the specifier reserves cannot name anything, so no position
// admits it.
inline void ExpectWordsFillNoIdentifierPosition(
    const char* spec, std::initializer_list<const char*> words,
    std::initializer_list<std::string_view> positions = {}) {
  for (const auto& p : kIdentifierPositions) {
    if (positions.size() != 0 && !PositionIsOneOf(p, positions)) continue;
    for (const char* word : words) {
      EXPECT_FALSE(ParseWithPreprocessorOk(In(spec, AtPosition(p, word))))
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
    for (const char* word : words) {
      std::string src = AtPosition(p, word);
      EXPECT_TRUE(ParseWithPreprocessorOk(In(earlier, src)))
          << p.what << ": everything this version includes leaves " << word
          << " free";
      EXPECT_FALSE(ParseWithPreprocessorOk(In(spec, src)))
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

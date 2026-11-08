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
#include "parser/ast_module.h"

using namespace delta;

struct PositionReport {
  const char* message;
  uint32_t body_line;
  const char* subclause;
};

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

inline void ExpectWordsFillNoIdentifierPosition(
    const char* spec, std::initializer_list<const char*> words,
    std::initializer_list<std::string_view> positions = {}) {
  for (const auto& p : kIdentifierPositions) {
    if (positions.size() != 0 && !PositionIsOneOf(p, positions)) continue;
    const PositionReport kRep = ReportForPosition(p);
    for (const char* word : words) {
      auto r = ParseWithPreprocessor(In(spec, AtPosition(p, word)));
      EXPECT_TRUE(ReportedError(r.diags, kRep.message,
                                LineInRegion(kRep.body_line), kRep.subclause))
          << word << " cannot name a " << p.what << " under this version";
    }
  }
}

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

inline void ExpectUnlistedWordNamesDesignElement(const char* spec,
                                                 const char* word) {
  std::string as_module = std::string("module ") + word + ";\nendmodule\n";
  auto named_module = ParseWithPreprocessor(In(spec, as_module));
  ASSERT_NE(named_module.cu, nullptr) << word;
  EXPECT_FALSE(named_module.has_errors) << word;
  ASSERT_EQ(named_module.cu->modules.size(), 1u) << word;
  EXPECT_EQ(named_module.cu->modules[0]->name, word);
}

inline void ExpectUnlistedWordNamesPort(const char* spec, const char* word) {
  std::string as_port = std::string("module m (input wire ") + word +
                        ", output wire y);\n  assign y = " + word +
                        ";\nendmodule\n";
  auto named_port = ParseWithPreprocessor(In(spec, as_port));
  ASSERT_NE(named_port.cu, nullptr) << word;
  EXPECT_FALSE(named_port.has_errors) << word;
  ASSERT_EQ(named_port.cu->modules[0]->ports.size(), 2u) << word;
  EXPECT_EQ(named_port.cu->modules[0]->ports[0].name, word);
}

inline void ExpectUnlistedWordNamesInstance(const char* spec,
                                            const char* word) {
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
}

inline void ExpectUnlistedWordNamesTaskAndBlock(const char* spec,
                                                const char* word) {
  std::string as_task = std::string("module m;\n  reg [7:0] r;\n  task ") +
                        word + "; r = 8'd1; endtask\n  initial begin : blk " +
                        word + "; end\nendmodule\n";
  EXPECT_TRUE(ParseWithPreprocessorOk(In(spec, as_task))) << word;

  std::string as_block =
      std::string("module m;\n  reg [7:0] r;\n  initial begin : ") + word +
      " r = 8'd1; end\nendmodule\n";
  EXPECT_TRUE(ParseWithPreprocessorOk(In(spec, as_block))) << word;
}

inline void ExpectUnlistedWordsNameEveryEntity(
    const char* spec, std::initializer_list<const char*> words) {
  for (const char* word : words) {
    ExpectUnlistedWordNamesDesignElement(spec, word);
    ExpectUnlistedWordNamesPort(spec, word);
    ExpectUnlistedWordNamesInstance(spec, word);
    ExpectUnlistedWordNamesTaskAndBlock(spec, word);
  }
}

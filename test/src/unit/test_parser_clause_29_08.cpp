// Tests for §29.8 — UDP instances

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult Parse(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static bool FindModuleInst(const std::vector<ModuleItem*>& items,
                           std::string_view module_name,
                           std::string_view expected_inst_name) {
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kModuleInst &&
        item->inst_module == module_name) {
      EXPECT_EQ(item->inst_name, expected_inst_name);
      return true;
    }
  }
  return false;
}

TEST(ParserSection29, UdpInstance) {
  auto r = Parse(
      "primitive inv(output out, input in);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n"
      "module top;\n"
      "  wire a, b;\n"
      "  inv u1(a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->udps.size(), 1);
  ASSERT_EQ(r.cu->modules.size(), 1);
  EXPECT_TRUE(FindModuleInst(r.cu->modules[0]->items, "inv", "u1"));
}

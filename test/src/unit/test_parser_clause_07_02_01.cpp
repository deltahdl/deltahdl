// §7.2.1: Packed structures

#include <gtest/gtest.h>
#include <string>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---
struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

};

namespace {

TEST(ParserAnnexA, A2TypedefStructPacked) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] addr;\n"
      "    logic [31:0] data;\n"
      "  } req_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kTypedef);
}

// struct_union [packed [signing]] { ... } {packed_dimension}
TEST(ParserA221, DataTypeStructPacked) {
  auto r = Parse(
      "module m;\n"
      "  struct packed signed { logic [7:0] a; logic [7:0] b; } pair;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kStruct);
  EXPECT_TRUE(item->data_type.is_packed);
  EXPECT_TRUE(item->data_type.is_signed);
}

}  // namespace

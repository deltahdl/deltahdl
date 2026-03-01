// §6.11: Integer data types

#include "fixture_parser.h"

using namespace delta;

struct ParseResult616 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult616 Parse(const std::string& src) {
  ParseResult616 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static ModuleItem* FirstItem(ParseResult616& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

namespace {

TEST(ParserSection6, IntegerTypeTimeDecl) {
  // 'time' is 4-state, 64-bit unsigned (LRM 6.11)
  auto r = Parse(
      "module m;\n"
      "  time t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTime);
  EXPECT_EQ(item->name, "t");
}

struct ParseResult6h {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult6h Parse(const std::string& src) {
  ParseResult6h result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static ModuleItem* FirstItem(ParseResult6h& r) {
  if (!r.cu || r.cu->modules.empty() || r.cu->modules[0]->items.empty())
    return nullptr;
  return r.cu->modules[0]->items[0];
}

// 16. Integer types as function return types.
TEST(ParserSection6, Sec6_11_ByteFunctionReturnType) {
  auto r = Parse(
      "module t;\n"
      "  function byte get_byte();\n"
      "    return 8'hAB;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kByte);
}

// 17. Integer types in task ports.
TEST(ParserSection6, Sec6_11_IntegerTypesInTaskPorts) {
  auto r = Parse(
      "module t;\n"
      "  task t1(input int x, output longint y);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[0].data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[1].data_type.kind, DataTypeKind::kLongint);
  EXPECT_EQ(item->func_args[1].direction, Direction::kOutput);
}

}  // namespace

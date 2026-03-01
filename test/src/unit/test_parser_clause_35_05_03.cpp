// §35.5.3: Context tasks and functions

#include "fixture_program.h"
#include "fixture_simulator.h"

using namespace delta;

using DpiParseTest = ProgramTestParse;

using ApiParseTest = ProgramTestParse;

struct ParseResult38 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ModuleItem* FindItemByKind(ParseResult38& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

struct ParseResult40 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult40 Parse(const std::string& src) {
  ParseResult40 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

namespace {

TEST(ParserSection38, DpiImportForVpiAccess) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" context function void\n"
      "    set_value(input int handle, input int val);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* dpi = FindItemByKind(r, ModuleItemKind::kDpiImport);
  ASSERT_NE(dpi, nullptr);
  EXPECT_EQ(dpi->name, "set_value");
  EXPECT_TRUE(dpi->dpi_is_context);
}

TEST(ParserSection38, DpiImportContextCallbackWithArgs) {
  // Context function with arguments typical for VPI callback registration
  auto r = Parse(R"(
    module m;
      import "DPI-C" context function int register_cb_wrapper(
        input int reason, input string user_data
      );
    endmodule
  )");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_TRUE(items[0]->dpi_is_context);
  EXPECT_EQ(items[0]->name, "register_cb_wrapper");
}

}  // namespace

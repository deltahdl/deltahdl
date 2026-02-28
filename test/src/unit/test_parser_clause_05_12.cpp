// §5.12: Attributes

#include "fixture_program.h"
#include "fixture_simulator.h"

using namespace delta;

using DpiParseTest = ProgramTestParse;

using ApiParseTest = ProgramTestParse;

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

// =============================================================================
// §35.2.1 Attributes on modules/instances
// =============================================================================
TEST_F(DpiParseTest, AttributeOnModuleDefinition) {
  auto* unit = Parse(R"(
    (* optimize_power *)
    module m;
      wire a;
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_EQ(unit->modules[0]->name, "m");
}

TEST_F(DpiParseTest, AttributeOnModuleInstantiation) {
  auto* unit = Parse(R"(
    module m;
      (* dont_touch *)
      sub u1(.a(x));
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kModuleInst);
  ASSERT_FALSE(items[0]->attrs.empty());
  EXPECT_EQ(items[0]->attrs[0].name, "dont_touch");
}

}  // namespace

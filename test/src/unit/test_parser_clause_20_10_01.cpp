// §20.10.1: Elaboration severity system tasks

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"

using namespace delta;

struct ParseResult21 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult21 Parse(const std::string& src) {
  ParseResult21 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

namespace {

// =============================================================================
// A.1.4 Module items
// =============================================================================
// severity_system_task: $fatal with finish_number and arguments.
TEST(SourceText, ElabSeverityFatal) {
  auto r = Parse(
      "module m;\n"
      "  $fatal(1, \"assertion failed\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kElabSystemTask);
}

// severity_system_task: all four forms ($fatal, $error, $warning, $info).
TEST(SourceText, ElabSeverityAllForms) {
  auto r = Parse(
      "module m;\n"
      "  $fatal;\n"
      "  $error(\"err\");\n"
      "  $warning(\"warn\");\n"
      "  $info;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 4u);
  for (size_t i = 0; i < 4; ++i) {
    EXPECT_EQ(r.cu->modules[0]->items[i]->kind,
              ModuleItemKind::kElabSystemTask);
  }
}

using ProgramParseTest = ProgramTestParse;

// Returns true if any item in the list matches the given kind.
bool HasItemKind(const std::vector<ModuleItem*>& items, ModuleItemKind kind) {
  for (auto* item : items) {
    if (item->kind == kind) return true;
  }
  return false;
}

// program_generate_item ::= elaboration_severity_system_task
TEST(SourceText, ProgramElabSeverityTask) {
  auto r = Parse(
      "program prg;\n"
      "  $info(\"program loaded\");\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(
      HasItemKind(r.cu->programs[0]->items, ModuleItemKind::kElabSystemTask));
}

}  // namespace

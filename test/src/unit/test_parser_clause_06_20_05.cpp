// §6.20.5: Specify parameters

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA24, SpecparamAssignmentMintypmax) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam tDelay = 1:2:3;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// specparam_declaration as non_port_module_item (outside specify block).
TEST(SourceText, SpecparamAsModuleItem) {
  auto r = Parse(
      "module m;\n"
      "  specparam delay = 10;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kSpecparam);
}

struct ParseResult6 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult6 Parse(const std::string& src) {
  ParseResult6 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

// --- specparam_assignment ---
// specparam_identifier = constant_mintypmax_expression
// | pulse_control_specparam
TEST(ParserA24, SpecparamAssignmentBasic) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam tRise = 10;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace

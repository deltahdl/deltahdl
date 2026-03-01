// Annex A.1.2: SystemVerilog source text

#include "fixture_parser.h"

using namespace delta;

namespace {

// description: { attribute_instance } package_item (file-scope function/task)
TEST(SourceText, DescriptionPackageItem) {
  auto r = Parse("function int add(int a, int b); return a + b; endfunction\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->cu_items.size(), 1u);
}

// =============================================================================
// A.1.2 comprehensive: all description types in one source text.
// =============================================================================
TEST(SourceText, AllDescriptionTypes) {
  auto r = Parse(
      "package pkg; endpackage\n"
      "module m; endmodule\n"
      "interface ifc; endinterface\n"
      "program prg; endprogram\n"
      "class C; endclass\n"
      "checker chk; endchecker\n"
      "primitive my_udp(output y, input a);\n"
      "  table 0 : 0 ; 1 : 1 ; endtable\n"
      "endprimitive\n"
      "config cfg;\n"
      "  design work.m;\n"
      "  default liblist work;\n"
      "endconfig\n"
      "bind m chk chk_i(.a(s));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives.size(), 1u);
}

TEST(ParserAnnexA, A1ProgramDecl) {
  auto r = Parse(
      "program test_prog(input logic clk);\n"
      "  initial $display(\"Hello\");\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "test_prog");
}

TEST(ParserAnnexA, A1CompilationUnitMultipleItems) {
  auto r = Parse(
      "package p; endpackage\n"
      "module m; endmodule\n"
      "interface i; endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->interfaces.size(), 1u);
}

// --- udp_declaration: coexistence with modules ---
TEST(ParserAnnexA051, UdpWithModule) {
  auto r = Parse(
      "primitive inv(output out, input in);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n"
      "module top;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

using SpecifyParseTest = ProgramTestParse;

// =============================================================================
// Parser test fixture
// =============================================================================
struct SpecifyTest : ::testing::Test {
 protected:
  CompilationUnit* Parse(const std::string& src) {
    source_ = src;
    lexer_ = std::make_unique<Lexer>(source_, 0, diag_);
    parser_ = std::make_unique<Parser>(*lexer_, arena_, diag_);
    return parser_->Parse();
  }

  // Helper: get first specify block from first module.
  ModuleItem* FirstSpecifyBlock(CompilationUnit* cu) {
    for (auto* item : cu->modules[0]->items) {
      if (item->kind == ModuleItemKind::kSpecifyBlock) return item;
    }
    return nullptr;
  }

  SourceManager mgr_;
  Arena arena_;
  DiagEngine diag_{mgr_};
  std::string source_;
  std::unique_ptr<Lexer> lexer_;
  std::unique_ptr<Parser> parser_;
};

struct ParseResult30 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult30 Parse(const std::string& src) {
  ParseResult30 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

TEST(ParserSection29, UdpCoexistsWithModule) {
  auto r = Parse(
      "primitive inv(output out, input in);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n"
      "module top;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->udps.size(), 1);
  ASSERT_EQ(r.cu->modules.size(), 1);
}

struct ParseResult31 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult31 Parse(const std::string& src) {
  ParseResult31 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

using ConfigParseTest = ProgramTestParse;

TEST_F(ConfigParseTest, ConfigCoexistsWithModule) {
  auto* unit = Parse(R"(
    module m;
    endmodule
    config cfg;
      design lib.top;
    endconfig
  )");
  EXPECT_EQ(unit->modules.size(), 1u);
  EXPECT_EQ(unit->configs.size(), 1u);
  EXPECT_EQ(unit->configs[0]->name, "cfg");
}

}  // namespace

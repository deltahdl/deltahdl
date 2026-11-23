#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_reported_error.h"
#include "lexer/lexer.h"
#include "parser/ast_design.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ParseFixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
};

static CompilationUnit* ParseSrc(const std::string& src, ParseFixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  return parser.Parse();
}

TEST(IdentifierSyntaxParsing, HierarchicalParameterIdentifierAcrossModule) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module sub;\n"
      "  parameter int WIDTH = 8;\n"
      "endmodule\n"
      "module m;\n"
      "  sub u();\n"
      "  logic [u.WIDTH-1:0] bus;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, HierarchicalEventIdentifierAcrossModule) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module sub;\n"
      "  event ev;\n"
      "endmodule\n"
      "module m;\n"
      "  sub u();\n"
      "  initial @(u.ev);\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, TopmoduleIdentifierInConfigDesign) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "config cfg;\n"
      "  design top_design;\n"
      "endconfig\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  ASSERT_EQ(cu->configs.size(), 1u);
  ASSERT_EQ(cu->configs[0]->design_cells.size(), 1u);
  EXPECT_EQ(cu->configs[0]->design_cells[0].cell, "top_design");
}

TEST(IdentifierSyntaxParsing, CellIdentifierInConfigCellRule) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "config cfg;\n"
      "  design top_design;\n"
      "  cell adder use fast_adder;\n"
      "endconfig\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  ASSERT_EQ(cu->configs.size(), 1u);
  ASSERT_EQ(cu->configs[0]->rules.size(), 1u);
  EXPECT_EQ(cu->configs[0]->rules[0]->cell_name, "adder");
}

TEST(IdentifierSyntaxParsing, CheckerIdentifierInCheckerDecl) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "checker chk;\n"
      "endchecker\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  ASSERT_EQ(cu->checkers.size(), 1u);
  EXPECT_EQ(cu->checkers[0]->name, "chk");
}

TEST(IdentifierSyntaxParsing, DynamicArrayVariableIdentifierDecl) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  int dyn_arr [];\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, RsProductionIdentifierInRandsequence) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  initial begin\n"
      "    randsequence (root_prod)\n"
      "      root_prod : leaf_prod ;\n"
      "      leaf_prod : { $display(\"leaf\"); } ;\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, SignalIdentifierInClockingBlock) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "module m(input clk, input a, input b);\n"
      "  clocking cb @(posedge clk);\n"
      "    input a, b;\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, PsCheckerIdentifierFromPackage) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "package pkg;\n"
      "  checker chk;\n"
      "  endchecker\n"
      "endpackage\n"
      "module m;\n"
      "  initial $display(\"%d\", pkg::chk);\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, PsCovergroupIdentifierFromPackage) {
  ParseFixture f;
  auto* cu = ParseSrc(
      "package pkg;\n"
      "  int x;\n"
      "  covergroup cg;\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "endpackage\n"
      "module m;\n"
      "  pkg::cg inst = new();\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(IdentifierSyntaxParsing, ANonAsciiLetterInASimpleIdentifierIsReported) {
  ParseFixture plain;
  ASSERT_NE(ParseSrc("module m;\n  logic cafe;\nendmodule\n", plain), nullptr);
  EXPECT_FALSE(plain.diag.HasErrors());

  ParseFixture f;
  ParseSrc("module m;\n  logic caf\xC3\xA9;\nendmodule\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "unexpected character 0xC3",
                            2, "5.2"));
}

struct DpiNameCase {
  const char* decl;
  const char* message;
  const char* subclause;
};

TEST(IdentifierSyntaxParsing, ADpiNameThatIsNoCIdentifierIsReported) {
  const DpiNameCase kCases[] = {
      {"export \"DPI-C\" 9bad = function f;",
       "expected 'function', got integer literal", "35.7"},
      {"import \"DPI-C\" $bad = function void g();",
       "expected 'function', got system identifier", "35.5.4"},
      {"export \"DPI-C\" $bad = function f;",
       "expected 'function', got system identifier", "35.7"},
      {"import \"DPI-C\" = function void g();", "expected 'function', got '='",
       "35.5.4"},
      {"export \"DPI-C\" = function f;", "expected 'function', got '='",
       "35.7"},
      {"import \"DPI-C\" foo bar = function void g();",
       "expected 'function', got identifier", "35.5.4"},
      {"export \"DPI-C\" foo bar = function f;",
       "expected 'function', got identifier", "35.7"},
  };
  for (const DpiNameCase& c : kCases) {
    ParseFixture f;
    ParseSrc(
        std::string("module m;\n  function int f(); return 1; endfunction\n"
                    "  ") +
            c.decl + "\nendmodule\n",
        f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), c.message, 3, c.subclause))
        << c.decl;
  }
}

}  // namespace

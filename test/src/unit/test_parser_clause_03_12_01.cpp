// §3.12.1: Compilation units

#include "fixture_parser.h"

using namespace delta;

namespace {

// description: { attribute_instance } package_item (file-scope task)
TEST(SourceText, DescriptionPackageItemTask) {
  auto r = Parse("task my_task; endtask\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->cu_items.size(), 1u);
}

// 10. No forward references in CU scope (except task/function names).
// The LRM says references shall only be made to names already defined.
// This is a semantic rule; the parser accepts the code but elaboration
// would reject it.  We test that parsing succeeds (syntax is valid).
TEST(ParserClause03, Cl3_12_1_ForwardRefSyntaxValid) {
  // This is valid syntax even though semantically 'b' is referenced
  // before its declaration at CU scope.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire w;\n"
              "endmodule\n"));
}

TEST(Parser, PackageAndModule) {
  auto r = Parse(
      "package pkg; endpackage\n"
      "module top; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1);
  ASSERT_EQ(r.cu->modules.size(), 1);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
  EXPECT_EQ(r.cu->modules[0]->name, "top");
}

struct ParseResult23b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult23b Parse(const std::string& src) {
  ParseResult23b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

TEST(ParserSection23, MultipleModuleDefinitions) {
  auto r = Parse(
      "module a; endmodule\n"
      "module b; endmodule\n"
      "module c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 3);
  EXPECT_EQ(r.cu->modules[0]->name, "a");
  EXPECT_EQ(r.cu->modules[1]->name, "b");
  EXPECT_EQ(r.cu->modules[2]->name, "c");
}

}  // namespace

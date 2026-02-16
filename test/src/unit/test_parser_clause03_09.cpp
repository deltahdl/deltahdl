#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

struct ParseResult3_09 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult3_09 Parse(const std::string& src) {
  ParseResult3_09 result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Preprocessor preproc(result.mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = result.mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(result.mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// LRM section 3.9 -- Packages
// =============================================================================

// §3.9: "Packages provide a declaration space, which can be shared by other
//        building blocks." Package with typedef, functions, and end label.
TEST(ParserSection3, Sec3_9_PackageDeclarationsAndEndLabel) {
  auto r = Parse(
      "package ComplexPkg;\n"
      "  typedef struct { shortreal i, r; } Complex;\n"
      "  function automatic int helper(int x); return x; endfunction\n"
      "endpackage : ComplexPkg\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "ComplexPkg");
  bool has_typedef = false, has_func = false;
  for (const auto* item : r.cu->packages[0]->items) {
    if (item->kind == ModuleItemKind::kTypedef) has_typedef = true;
    if (item->kind == ModuleItemKind::kFunctionDecl) has_func = true;
  }
  EXPECT_TRUE(has_typedef);
  EXPECT_TRUE(has_func);
}

// §3.9: "Package declarations can be imported into other building blocks,
//        including other packages."
TEST(ParserSection3, Sec3_9_ImportIntoModuleAndPackage) {
  auto r = Parse(
      "package A; typedef int myint; endpackage\n"
      "package B; import A::*; endpackage\n"
      "module m; import A::myint; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 2u);
  EXPECT_EQ(r.cu->packages[0]->name, "A");
  EXPECT_EQ(r.cu->packages[1]->name, "B");
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

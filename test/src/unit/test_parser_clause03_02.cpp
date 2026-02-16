#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

struct ParseResult3_02 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult3_02 Parse(const std::string& src) {
  ParseResult3_02 result;
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

static bool ParseOk(const std::string& src) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", src);
  Preprocessor preproc(mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

// =============================================================================
// LRM section 3.2 -- Design elements
// =============================================================================

TEST(ParserSection3, AllSevenDesignElements) {
  // §3.2: A design element is a module, program, interface, checker,
  //       package, primitive, or configuration.
  auto r = Parse(
      "module m; endmodule\n"
      "program p; endprogram\n"
      "interface ifc; endinterface\n"
      "checker chk; endchecker\n"
      "package pkg; endpackage\n"
      "primitive udp_and (output out, input a, b);\n"
      "  table 0 0 : 0; 0 1 : 0; 1 0 : 0; 1 1 : 1; endtable\n"
      "endprimitive\n"
      "config cfg; design m; endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
  EXPECT_EQ(r.cu->modules[0]->decl_kind, ModuleDeclKind::kModule);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "p");
  EXPECT_EQ(r.cu->programs[0]->decl_kind, ModuleDeclKind::kProgram);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->name, "ifc");
  EXPECT_EQ(r.cu->interfaces[0]->decl_kind, ModuleDeclKind::kInterface);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "chk");
  EXPECT_EQ(r.cu->checkers[0]->decl_kind, ModuleDeclKind::kChecker);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->name, "udp_and");
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->name, "cfg");
  // Multiple design elements of same type in one compilation unit
  EXPECT_TRUE(ParseOk("module a; endmodule\nmodule b; endmodule\n"));
  // Module + package coexist in same unit with import
  EXPECT_TRUE(
      ParseOk("package p; typedef int myint; endpackage\n"
              "module m; import p::*; endmodule\n"));
}

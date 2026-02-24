// §23.11: Binding auxiliary code to scopes or instances

#include <gtest/gtest.h>
#include <string>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---
struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

// =============================================================================
// A.1.2 bind_directive (§23.11)
// =============================================================================
// Form 1: bind target_scope bind_instantiation
TEST(SourceText, BindDirectiveBasic) {
  auto r = Parse("bind target_mod checker_mod chk_inst(.a(sig));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives[0]->target, "target_mod");
  EXPECT_TRUE(r.cu->bind_directives[0]->target_instances.empty());
  ASSERT_NE(r.cu->bind_directives[0]->instantiation, nullptr);
  EXPECT_EQ(r.cu->bind_directives[0]->instantiation->inst_module,
            "checker_mod");
  EXPECT_EQ(r.cu->bind_directives[0]->instantiation->inst_name, "chk_inst");
}

// Form 1 with instance list: bind scope : inst1, inst2 instantiation
TEST(SourceText, BindDirectiveWithInstanceList) {
  auto r = Parse("bind dut : i1, i2 chk chk_i(.clk(clk));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives[0]->target, "dut");
  ASSERT_EQ(r.cu->bind_directives[0]->target_instances.size(), 2u);
  EXPECT_EQ(r.cu->bind_directives[0]->target_instances[0], "i1");
  EXPECT_EQ(r.cu->bind_directives[0]->target_instances[1], "i2");
}

// Form 2: bind hierarchical_instance instantiation
TEST(SourceText, BindDirectiveHierarchical) {
  auto r = Parse("bind top.dut.u1 checker_mod chk(.a(sig));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives[0]->target, "top.dut.u1");
}

// Bind with parameterized instantiation.
TEST(SourceText, BindDirectiveParameterized) {
  auto r = Parse("bind target_mod my_checker #(8) chk_i(.clk(clk));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  auto *inst = r.cu->bind_directives[0]->instantiation;
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->inst_params.size(), 1u);
}

// Bind stores source location.
TEST(SourceText, BindDirectiveHasSourceLoc) {
  auto r = Parse("bind target_mod chk chk_i(.a(s));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_NE(r.cu->bind_directives[0]->loc.line, 0u);
}

// Multiple bind directives.
TEST(SourceText, MultipleBindDirectives) {
  auto r = Parse(
      "bind mod1 chk1 c1(.a(s));\n"
      "bind mod2 chk2 c2(.a(s));\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 2u);
  EXPECT_EQ(r.cu->bind_directives[0]->target, "mod1");
  EXPECT_EQ(r.cu->bind_directives[1]->target, "mod2");
}

// Bind mixed with other top-level descriptions.
TEST(SourceText, BindMixedWithOtherDescriptions) {
  auto r = Parse(
      "module m; endmodule\n"
      "bind m checker_mod chk_i(.a(sig));\n"
      "package p; endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_EQ(r.cu->packages.size(), 1u);
}

}  // namespace

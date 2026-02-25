// §6.20.2: Value parameters

#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ElabA83Fixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  bool has_errors = false;
};

static RtlirDesign* ElaborateSrc(const std::string& src, ElabA83Fixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(cu->modules.back()->name);
  f.has_errors = f.diag.HasErrors();
  return design;
}

namespace {

// § constant_expression — binary op in parameter elaborates
TEST(ElabA83, ConstantBinaryExprInParamElaborates) {
  ElabA83Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int WIDTH = 4 + 4;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// =============================================================================
// A.8.4 Primaries — Elaboration
// =============================================================================
// § constant_primary — integer literal in parameter elaborates
TEST(ElabA84, ConstantPrimaryIntegerLiteral) {
  ElabA84Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int P = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § constant_primary — real literal in parameter elaborates
TEST(ElabA84, ConstantPrimaryRealLiteral) {
  ElabA84Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter real R = 3.14;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § constant_primary — parameter reference elaborates
TEST(ElabA84, ConstantPrimaryParameterRef) {
  ElabA84Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int A = 5;\n"
      "  parameter int B = A;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace

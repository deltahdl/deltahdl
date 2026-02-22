// Tests for A.8.4 — Primaries — Elaboration

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

namespace {

struct ElabA84Fixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  bool has_errors = false;
};

static RtlirDesign *ElaborateSrc(const std::string &src, ElabA84Fixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto *design = elab.Elaborate(cu->modules.back()->name);
  f.has_errors = f.diag.HasErrors();
  return design;
}

}  // namespace

// =============================================================================
// A.8.4 Primaries — Elaboration
// =============================================================================

// § constant_primary — integer literal in parameter elaborates

TEST(ElabA84, ConstantPrimaryIntegerLiteral) {
  ElabA84Fixture f;
  auto *design = ElaborateSrc(
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
  auto *design = ElaborateSrc(
      "module m;\n"
      "  parameter real R = 3.14;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § constant_primary — string literal in parameter elaborates

TEST(ElabA84, ConstantPrimaryStringLiteral) {
  ElabA84Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  parameter string S = \"hello\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § constant_primary — parameter reference elaborates

TEST(ElabA84, ConstantPrimaryParameterRef) {
  ElabA84Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  parameter int A = 5;\n"
      "  parameter int B = A;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § constant_primary — cast elaborates

TEST(ElabA84, ConstantPrimaryCastElaborates) {
  ElabA84Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  parameter int P = int'(3.14);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § primary — hierarchical identifier with select elaborates

TEST(ElabA84, PrimaryHierIdentSelectElaborates) {
  ElabA84Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  logic x;\n"
      "  initial x = data[3];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § primary — concatenation elaborates

TEST(ElabA84, PrimaryConcatenationElaborates) {
  ElabA84Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  logic [15:0] c;\n"
      "  initial c = {a, b};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § primary — function call elaborates

TEST(ElabA84, PrimaryFunctionCallElaborates) {
  ElabA84Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  function int foo(int a); return a + 1; endfunction\n"
      "  int x;\n"
      "  initial x = foo(5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § primary — cast in initial elaborates

TEST(ElabA84, PrimaryCastInInitialElaborates) {
  ElabA84Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  int b;\n"
      "  initial b = int'(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § primary — null elaborates

TEST(ElabA84, PrimaryNullElaborates) {
  ElabA84Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    automatic int x;\n"
      "    x = null;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § primary — unbased_unsized_literal elaborates

TEST(ElabA84, PrimaryUnbasedUnsizedElaborates) {
  ElabA84Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  assign x = '1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § primary — streaming concatenation elaborates

TEST(ElabA84, PrimaryStreamingConcatElaborates) {
  ElabA84Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] a;\n"
      "  logic [31:0] b;\n"
      "  initial b = {<< 8 {a}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § primary_literal — part select range elaborates

TEST(ElabA84, PrimaryPartSelectRangeElaborates) {
  ElabA84Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] data;\n"
      "  logic [7:0] x;\n"
      "  initial x = data[15:8];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § primary — system call elaborates

TEST(ElabA84, PrimarySystemCallElaborates) {
  ElabA84Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  parameter int W = $clog2(16);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

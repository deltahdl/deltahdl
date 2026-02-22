// Tests for A.8.7 — Numbers — Elaboration

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

struct ElabA87Fixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  bool has_errors = false;
};

static RtlirDesign *ElaborateSrc(const std::string &src, ElabA87Fixture &f) {
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
// A.8.7 Numbers — Elaboration
// =============================================================================

// § number — integral_number elaborates

TEST(ElabA87, NumberIntegralElaborates) {
  ElabA87Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § number — real_number elaborates

TEST(ElabA87, NumberRealElaborates) {
  ElabA87Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  real x;\n"
      "  initial x = 3.14;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § integral_number — decimal_number (unsized) elaborates

TEST(ElabA87, DecimalUnsizedElaborates) {
  ElabA87Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  parameter int P = 255;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § integral_number — binary_number elaborates

TEST(ElabA87, BinaryNumberElaborates) {
  ElabA87Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'b10101010;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § integral_number — octal_number elaborates

TEST(ElabA87, OctalNumberElaborates) {
  ElabA87Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'o77;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § integral_number — hex_number elaborates

TEST(ElabA87, HexNumberElaborates) {
  ElabA87Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'hFF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § decimal_number — sized with decimal_base elaborates

TEST(ElabA87, DecimalSizedBaseElaborates) {
  ElabA87Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd200;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § decimal_number — x_digit elaborates

TEST(ElabA87, DecimalXDigitElaborates) {
  ElabA87Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'dx;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § decimal_number — z_digit elaborates

TEST(ElabA87, DecimalZDigitElaborates) {
  ElabA87Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'dz;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § signed bases elaborate — 'sd, 'sb, 'so, 'sh

TEST(ElabA87, SignedDecimalElaborates) {
  ElabA87Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'sd99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabA87, SignedBinaryElaborates) {
  ElabA87Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic [3:0] x;\n"
      "  initial x = 4'sb1010;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabA87, SignedOctalElaborates) {
  ElabA87Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'so77;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabA87, SignedHexElaborates) {
  ElabA87Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'shAB;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § real_number — fixed_point_number elaborates

TEST(ElabA87, FixedPointElaborates) {
  ElabA87Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  real x;\n"
      "  initial x = 2.718;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § real_number — scientific notation elaborates

TEST(ElabA87, ScientificNotationElaborates) {
  ElabA87Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  real x;\n"
      "  initial x = 1.5e+3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § unsigned_number — underscored decimal elaborates

TEST(ElabA87, UnderscoredDecimalElaborates) {
  ElabA87Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  int x;\n"
      "  initial x = 1_000;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § unbased_unsized_literal — '0, '1, 'x, 'z elaborate

TEST(ElabA87, UnbasedUnsizedZeroElaborates) {
  ElabA87Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial x = '0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabA87, UnbasedUnsizedOneElaborates) {
  ElabA87Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial x = '1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabA87, UnbasedUnsizedXElaborates) {
  ElabA87Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial x = 'x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabA87, UnbasedUnsizedZElaborates) {
  ElabA87Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial x = 'z;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

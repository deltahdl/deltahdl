// Tests for A.7.5.2 — System timing check command arguments — Elaboration

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

struct ElabA70502Fixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  bool has_errors = false;
};

static RtlirDesign* ElaborateSrc(const std::string& src, ElabA70502Fixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(cu->modules.back()->name);
  f.has_errors = f.diag.HasErrors();
  return design;
}

}  // namespace

// =============================================================================
// A.7.5.2 Elab — mintypmax timing check limits ($nochange offsets)
// =============================================================================

TEST(ElabA70502, NochangeMinTypMaxOffsetsElaborate) {
  ElabA70502Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $nochange(posedge clk, data, 1:2:3, 4:5:6);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// =============================================================================
// A.7.5.2 Elab — mintypmax timestamp_condition
// =============================================================================

TEST(ElabA70502, TimestampCondMinTypMaxElaborates) {
  ElabA70502Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setuphold(posedge clk, data, 10, 5, ntfr, 1:2:3);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// =============================================================================
// A.7.5.2 Elab — mintypmax timecheck_condition
// =============================================================================

TEST(ElabA70502, TimecheckCondMinTypMaxElaborates) {
  ElabA70502Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setuphold(posedge clk, data, 10, 5, ntfr, 1:2:3, 4:5:6);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// =============================================================================
// A.7.5.2 Elab — delayed_data with bracket expression
// =============================================================================

TEST(ElabA70502, DelayedDataWithBracketElaborates) {
  ElabA70502Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setuphold(posedge clk, data, 10, 5, ntfr, , , dCLK, dD[3]);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// =============================================================================
// A.7.5.2 Elab — delayed_reference with bracket mintypmax expression
// =============================================================================

TEST(ElabA70502, DelayedRefWithBracketMinTypMaxElaborates) {
  ElabA70502Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setuphold(posedge clk, data, 10, 5, ntfr, , , dCLK[1:2:3], dD);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// =============================================================================
// A.7.5.2 Elab — remain_active_flag as constant_mintypmax_expression
// =============================================================================

TEST(ElabA70502, RemainActiveFlagMinTypMaxElaborates) {
  ElabA70502Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $timeskew(posedge clk1, posedge clk2, 5, ntfr, 1, 1:2:3);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

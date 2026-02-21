// Tests for A.7.5.1 — System timing check commands — Elaboration

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

struct ElabA70501Fixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  bool has_errors = false;
};

static RtlirDesign* ElaborateSrc(const std::string& src, ElabA70501Fixture& f) {
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
// A.7.5.1 $setup_timing_check — command structure
// =============================================================================

TEST(ElabA70501, SetupWithNotifierElaborates) {
  ElabA70501Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data, posedge clk, 10, ntfr);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// =============================================================================
// A.7.5.1 $setuphold_timing_check — full 9-argument form
// =============================================================================

TEST(ElabA70501, SetupholdFullArgsElaborates) {
  ElabA70501Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setuphold(posedge clk, data, 10, 5, ntfr, , , dCLK, dDATA);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// =============================================================================
// A.7.5.1 $recrem_timing_check — full 9-argument form
// =============================================================================

TEST(ElabA70501, RecremFullArgsElaborates) {
  ElabA70501Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $recrem(posedge clk, rst, 8, 3, ntfr, , , dCLK, dRST);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// =============================================================================
// A.7.5.1 $timeskew_timing_check — with flags
// =============================================================================

TEST(ElabA70501, TimeskewWithFlagsElaborates) {
  ElabA70501Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $timeskew(posedge clk1, posedge clk2, 5, ntfr, 1, 0);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// =============================================================================
// A.7.5.1 $fullskew_timing_check — with flags
// =============================================================================

TEST(ElabA70501, FullskewWithFlagsElaborates) {
  ElabA70501Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $fullskew(posedge clk1, negedge clk2, 4, 6, ntfr, 1, 0);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// =============================================================================
// A.7.5.1 $width_timing_check — threshold argument
// =============================================================================

TEST(ElabA70501, WidthWithThresholdElaborates) {
  ElabA70501Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $width(posedge clk, 20, 1, ntfr);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// =============================================================================
// A.7.5.1 All 12 commands with full argument forms
// =============================================================================

TEST(ElabA70501, AllTwelveCommandFormsElaborate) {
  ElabA70501Fixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(d, posedge clk, 10, ntfr);\n"
      "    $hold(posedge clk, d, 5, ntfr);\n"
      "    $setuphold(posedge clk, d, 10, 5, ntfr, , , dCLK, dDATA);\n"
      "    $recovery(posedge clk, rst, 8, ntfr);\n"
      "    $removal(posedge clk, rst, 3, ntfr);\n"
      "    $recrem(posedge clk, rst, 8, 3, ntfr, , , dCLK, dRST);\n"
      "    $skew(posedge clk1, negedge clk2, 3, ntfr);\n"
      "    $timeskew(posedge clk1, posedge clk2, 5, ntfr, 1, 0);\n"
      "    $fullskew(posedge clk1, negedge clk2, 4, 6, ntfr, 1, 0);\n"
      "    $period(posedge clk, 50, ntfr);\n"
      "    $width(posedge clk, 20, 1, ntfr);\n"
      "    $nochange(posedge clk, d, 0, 0, ntfr);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

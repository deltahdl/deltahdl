// Tests for A.7.5.3 — System timing check event definitions — Elaboration

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

struct ElabA70503Fixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  bool has_errors = false;
};

static RtlirDesign *ElaborateSrc(const std::string &src, ElabA70503Fixture &f) {
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
// A.7.5.3 Elab — timing_check_event with edge controls
// =============================================================================

// timing_check_event with no edge elaborates
TEST(ElabA70503, TimingCheckEventNoEdgeElaborates) {
  ElabA70503Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data, clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// timing_check_event with posedge elaborates
TEST(ElabA70503, TimingCheckEventPosedgeElaborates) {
  ElabA70503Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data, posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// timing_check_event with negedge elaborates
TEST(ElabA70503, TimingCheckEventNegedgeElaborates) {
  ElabA70503Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $hold(negedge clk, data, 5);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// timing_check_event with edge keyword elaborates
TEST(ElabA70503, TimingCheckEventEdgeKeywordElaborates) {
  ElabA70503Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data, edge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// =============================================================================
// A.7.5.3 Elab — edge_control_specifier
// =============================================================================

// edge_control_specifier with 01, 10 descriptors elaborates
TEST(ElabA70503, EdgeControlSpecifier01_10Elaborates) {
  ElabA70503Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data, edge [01, 10] clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// edge_control_specifier with x transitions elaborates
TEST(ElabA70503, EdgeControlSpecifierXTransitionsElaborates) {
  ElabA70503Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data, edge [x0, x1] clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// =============================================================================
// A.7.5.3 Elab — specify_terminal_descriptor with ranges
// =============================================================================

// Terminal with bit select elaborates
TEST(ElabA70503, TerminalBitSelectElaborates) {
  ElabA70503Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data[0], posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Terminal with part select elaborates
TEST(ElabA70503, TerminalPartSelectElaborates) {
  ElabA70503Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data[3:0], posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Terminal with interface.port form elaborates
TEST(ElabA70503, TerminalInterfaceDotPortElaborates) {
  ElabA70503Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(intf.data, posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// =============================================================================
// A.7.5.3 Elab — timing_check_condition with &&&
// =============================================================================

// &&& bare condition elaborates
TEST(ElabA70503, TimingCheckConditionBareElaborates) {
  ElabA70503Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data &&& en, posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// &&& with parenthesized scalar_timing_check_condition elaborates
TEST(ElabA70503, TimingCheckConditionParenthesizedElaborates) {
  ElabA70503Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data &&& (en == 1'b1), posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// &&& with negation elaborates
TEST(ElabA70503, TimingCheckConditionNegationElaborates) {
  ElabA70503Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $setup(data &&& ~reset, posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// &&& on both ref and data events elaborates
TEST(ElabA70503, ConditionBothEventsElaborates) {
  ElabA70503Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $hold(posedge clk &&& en, data &&& reset, 5);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// =============================================================================
// A.7.5.3 Elab — controlled_timing_check_event
// =============================================================================

// $period with controlled_timing_check_event elaborates
TEST(ElabA70503, ControlledTimingCheckEventPeriodElaborates) {
  ElabA70503Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $period(posedge clk, 50);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// $width with controlled_timing_check_event and condition elaborates
TEST(ElabA70503, ControlledTimingCheckEventWidthCondElaborates) {
  ElabA70503Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $width(negedge rst &&& en, 20);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// =============================================================================
// A.7.5.3 Elab — combined edge + terminal range + condition
// =============================================================================

// Full combination: edge + bit-select terminal + &&& condition elaborates
TEST(ElabA70503, FullCombinationElaborates) {
  ElabA70503Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    $hold(posedge clk &&& en, data[0] &&& reset, 5);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "fixture_specify_manager.h"
#include "simulator/sdf_parser.h"
#include "simulator/specify.h"
#include "simulator/specify_internal.h"
#include "simulator/specify_path_delay.h"

using namespace delta;

namespace {

std::string TextOfCondition(const std::string& src, SimFixture& f) {
  return SpecifyConditionText(ParseExprFrom(src, f));
}

TEST(StateDependentPathConditionText, BitSelectConditionNamesVectorAndIndex) {
  SimFixture f;
  EXPECT_EQ(TextOfCondition("flag[3]", f), "flag[3]");
}

TEST(StateDependentPathConditionText, PartSelectConditionNamesBothBounds) {
  SimFixture f;
  EXPECT_EQ(TextOfCondition("sel[5:2]", f), "sel[5:2]");
}

TEST(StateDependentPathConditionText, ConcatenationConditionNamesEveryElement) {
  SimFixture f;
  EXPECT_EQ(TextOfCondition("{gate, hold}", f), "{gate, hold}");
}

TEST(StateDependentPathConditionText,
     ReplicationConditionNamesCountAndElement) {
  SimFixture f;
  EXPECT_EQ(TextOfCondition("{4{gate}}", f), "{4{gate}}");
}

TEST(StateDependentPathConditionText,
     ConditionalOperatorConditionNamesAllThreeOperands) {
  SimFixture f;
  EXPECT_EQ(TextOfCondition("hold ? gate : keep", f), "hold ? gate : keep");
}

TEST(StateDependentPathConditionText, CaretTildeXnorConditionKeepsItsSpelling) {
  SimFixture f;
  EXPECT_EQ(TextOfCondition("gate ^~ hold", f), "gate ^~ hold");
}

TEST(StateDependentPathConditionText, TildeCaretXnorConditionKeepsItsSpelling) {
  SimFixture f;
  EXPECT_EQ(TextOfCondition("gate ~^ hold", f), "gate ~^ hold");
}

TEST(StateDependentPathConditionText, ReductionNandConditionNamesItsOperand) {
  SimFixture f;
  EXPECT_EQ(TextOfCondition("~&gate", f), "~&gate");
}

TEST(StateDependentPathConditionText, ReductionNorConditionNamesItsOperand) {
  SimFixture f;
  EXPECT_EQ(TextOfCondition("~|hold", f), "~|hold");
}

TEST(StateDependentPathConditionText,
     AnOperatorOutsideTableThirtyOneRendersEmpty) {
  SimFixture f;
  EXPECT_EQ(TextOfCondition("mode < 5", f), "");
}

TEST(StateDependentPathConditionSpelling,
     APartSelectSpelledWithAndWithoutSpacesIsOneCondition) {
  EXPECT_TRUE(SpecifyConditionsMatch("mode[7 : 6]", "mode[7:6]"));
}

TEST(StateDependentPathConditionSpelling,
     ConditionsDifferingBeyondWhitespaceAreNotOneCondition) {
  EXPECT_FALSE(SpecifyConditionsMatch("mode[9 : 6]", "mode[7:6]"));
}

const char* const kTwoBitConditions =
    "module path_cond_cell(input src_a, input [3:0] mode, output dst_y);\n"
    "  specify\n"
    "    if (mode[3]) (src_a => dst_y) = 37;\n"
    "    if (mode[1]) (src_a => dst_y) = 41;\n"
    "  endspecify\n"
    "endmodule\n";

const char* const kXnorCondition =
    "module path_xnor_cell(input src_a, input sel_p, input sel_q,\n"
    "                      output dst_y);\n"
    "  specify\n"
    "    if (sel_p ~^ sel_q) (src_a => dst_y) = 31;\n"
    "    if (sel_p ^ sel_q) (src_a => dst_y) = 43;\n"
    "  endspecify\n"
    "endmodule\n";

const char* const kSpelledConditions =
    "module path_spell_cell(input src_a, input [7:0] mode, input en_hi,\n"
    "                       input en_lo, output dst_y);\n"
    "  specify\n"
    "    if (mode[7:6]) (src_a => dst_y) = 29;\n"
    "    if ({en_hi, en_lo}) (src_a => dst_y) = 23;\n"
    "  endspecify\n"
    "endmodule\n";

bool RegisterPathsOf(const char* src, SimFixture& f, SpecifyManager& mgr) {
  auto* cu = RunModuleSource(src, f);
  if (cu == nullptr) return false;
  RegisterPathDelays(*cu->modules.back(), f, mgr);
  return true;
}

void ApplySdfOnto(const std::string& sdf, SpecifyManager& mgr) {
  SdfFile file;
  ASSERT_TRUE(ParseSdf(sdf, file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);
}

std::string CellDelaySdf(const std::string& cell_type,
                         const std::string& entry) {
  return "(DELAYFILE (CELL (CELLTYPE \"" + cell_type +
         "\") (INSTANCE u_dut) (DELAY (ABSOLUTE " + entry + "))))";
}

const PathDelay* PathConditionedOn(const SpecifyManager& mgr,
                                   std::string_view condition) {
  for (const auto& pd : mgr.GetPathDelays()) {
    if (SpecifyConditionsMatch(pd.condition, condition)) return &pd;
  }
  return nullptr;
}

const PathDelay* AnnotatedSpelledPath(SimFixture& f, SpecifyManager& mgr,
                                      const std::string& sdf_entry,
                                      std::string_view condition) {
  if (!RegisterPathsOf(kSpelledConditions, f, mgr)) return nullptr;
  ApplySdfOnto(CellDelaySdf("path_spell_cell", sdf_entry), mgr);
  return PathConditionedOn(mgr, condition);
}

TEST(StateDependentPathConditionText,
     SdfCondOnABitSelectAnnotatesTheDeclaredPath) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(RegisterPathsOf(kTwoBitConditions, f, mgr));

  ApplySdfOnto(CellDelaySdf("path_cond_cell",
                            "(COND mode[3] (IOPATH src_a dst_y (53)))"),
               mgr);

  const PathDelay* selected = PathConditionedOn(mgr, "mode[3]");
  ASSERT_NE(selected, nullptr);
  EXPECT_EQ(selected->delays[0], 53u);
}

TEST(StateDependentPathConditionText,
     SdfCondOnABitSelectLeavesAnotherBitsPathAlone) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(RegisterPathsOf(kTwoBitConditions, f, mgr));

  ApplySdfOnto(CellDelaySdf("path_cond_cell",
                            "(COND mode[3] (IOPATH src_a dst_y (53)))"),
               mgr);

  const PathDelay* untouched = PathConditionedOn(mgr, "mode[1]");
  ASSERT_NE(untouched, nullptr);
  EXPECT_EQ(untouched->delays[0], 41u);
}

TEST(StateDependentPathConditionSpelling,
     SdfCondOnAPartSelectAnnotatesTheDeclaredPath) {
  SimFixture f;
  SpecifyManager mgr;

  const PathDelay* selected = AnnotatedSpelledPath(
      f, mgr, "(COND mode[7:6] (IOPATH src_a dst_y (61)))", "mode[7:6]");

  ASSERT_NE(selected, nullptr);
  EXPECT_EQ(selected->delays[0], 61u);
}

TEST(StateDependentPathConditionSpelling,
     SdfCondOnAnUnspacedConcatenationAnnotatesTheDeclaredPath) {
  SimFixture f;
  SpecifyManager mgr;

  const PathDelay* selected = AnnotatedSpelledPath(
      f, mgr, "(COND {en_hi,en_lo} (IOPATH src_a dst_y (59)))",
      "{en_hi, en_lo}");

  ASSERT_NE(selected, nullptr);
  EXPECT_EQ(selected->delays[0], 59u);
}

TEST(StateDependentPathConditionSpelling,
     SdfCondOnASpacedConcatenationAnnotatesTheDeclaredPath) {
  SimFixture f;
  SpecifyManager mgr;

  const PathDelay* selected = AnnotatedSpelledPath(
      f, mgr, "(COND {en_hi, en_lo} (IOPATH src_a dst_y (67)))",
      "{en_hi, en_lo}");

  ASSERT_NE(selected, nullptr);
  EXPECT_EQ(selected->delays[0], 67u);
}

TEST(StateDependentPathConditionText,
     SdfCondOnAnXnorAnnotatesTheDeclaredPathOnly) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(RegisterPathsOf(kXnorCondition, f, mgr));

  ApplySdfOnto(CellDelaySdf("path_xnor_cell",
                            "(COND sel_p ~^ sel_q (IOPATH src_a dst_y (71)))"),
               mgr);

  const PathDelay* xnor = PathConditionedOn(mgr, "sel_p ~^ sel_q");
  ASSERT_NE(xnor, nullptr);
  EXPECT_EQ(xnor->delays[0], 71u);
  const PathDelay* xor_path = PathConditionedOn(mgr, "sel_p ^ sel_q");
  ASSERT_NE(xor_path, nullptr);
  EXPECT_EQ(xor_path->delays[0], 43u);
}

}  // namespace

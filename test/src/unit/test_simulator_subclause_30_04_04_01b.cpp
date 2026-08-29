// Which §30.4.4.1 conditions can be written down for §32.4.1 to compare, and
// whether one condition spelled two ways compares equal.
//
// A state-dependent path carries its condition twice over: as the expression
// §30.5.3's activity test evaluates, and as the text §32.4.1 backannotation
// matches an SDF COND entry against. SpecifyConditionText in
// simulator/specify_condition_text.cpp writes the second one, and a condition
// it cannot spell comes out as the empty string. That is the same string an
// unconditional path carries, so a path whose condition renders to nothing is
// matched by no COND entry at all.
//
// Issue #3394 is that the bit-select, part-select, concatenation, replication
// and conditional-operator forms all came out that way, though
// §30.4.4.1 names bit-selects and part-selects of ports and of locally defined
// variables among the operands a condition may be built from, and Table 30-1
// (printed page 876) lists concatenation, replication and the conditional
// operator among the operators.
//
// The five cases at the top hand SpecifyConditionText one of those forms each
// and read the spelling back, which is the spelling an SDF file writes. Two
// cases further down run a design and annotate it, so the text is shown to be
// comparable against an SDF COND rather than merely non-empty.
//
// Issue #3400 is that a condition both sides can spell is still spelled
// differently by each. NextSdfToken in simulator/sdf_parser.cpp lexes ':' as a
// token of its own and LexIdent beside it runs to whitespace, so a COND written
// `mode[7:6]` reaches JoinSdfCondTokens as three tokens and is rejoined as
// `mode[7 : 6]`, while a COND written `{a,b}` reaches it as one token where
// `{a, b}` reaches it as two. SpecifyConditionText writes `mode[7:6]` and
// `{a, b}`, so comparing the two sides as strings answers no to the first pair
// and lets the file's spacing of a comma decide the second.
// SpecifyConditionsMatch, beside SpecifyConditionText, is what compares two
// conditions with whitespace ignored. Five cases are about it: two hand it the
// two spellings the two sides actually produce, and three run a design against
// an SDF file and read the annotated delay back.
//
// Every number here is picked so that no two quantities a case tells apart
// share a value. The direct cases select bit 3, the part-select bounds 5 and
// 2, and the replication count 4, so an index written where a bound belongs,
// a bound written in the other bound's place, or a count written as an index
// all read differently from the right answer, and none of them is the 0 that
// an address the renderer failed to read would leave behind. The design
// declares its mode[3] path at 37 and its mode[1] path at 41 while the file
// annotates 53, so a path that kept its declaration, a path that took the
// other path's value and a path that took the file's value are three
// different readings. The two bits it tests are 3 and 1 rather than 1 and 0,
// so neither bit number is 0 and neither equals the other, and a renderer
// that dropped the index would leave the two paths naming one condition.
//
// The spelling cases pick their literals on the same rule and share none of
// those. Their design declares its mode[7:6] path at 29 and its
// {en_hi, en_lo} path at 23, and the three SDF files annotate 61, 59 and 67, so
// no two of the delays a case could read share a value and a path that kept its
// declaration reads differently from one that took any file's value. The
// part-select bounds are 7 and 6, which differ from each other and from every
// index and bound above, and the vector is declared [7:0] so both bounds are in
// range. The case asserting two conditions are not one writes `mode[9 : 6]`
// against `mode[7:6]`, 9 being a value nothing else here uses, so what that
// case turns on is a digit rather than a space.

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "fixture_specify_manager.h"
#include "simulator/sdf_parser.h"
#include "simulator/specify.h"
#include "simulator/specify_internal.h"

using namespace delta;

namespace {

// The condition text SpecifyConditionText writes for the expression `src`
// spells. §30.4.4.1 states its operand and operator rules over the
// expression itself, so a case about one of those forms hands the function
// an expression parsed on its own rather than one read off a declaration.
std::string TextOfCondition(const std::string& src, SimFixture& f) {
  return SpecifyConditionText(ParseExprFrom(src, f));
}

// §30.4.4.1: a bit-select of a port is an operand, and an SDF COND names one
// as `name[index]`, so both the vector and the bit have to appear.
TEST(StateDependentPathConditionText, BitSelectConditionNamesVectorAndIndex) {
  SimFixture f;
  EXPECT_EQ(TextOfCondition("flag[3]", f), "flag[3]");
}

// §30.4.4.1: a part-select of a port is an operand, and an SDF COND names one
// as `name[msb:lsb]`, so both bounds have to appear in the order written.
TEST(StateDependentPathConditionText, PartSelectConditionNamesBothBounds) {
  SimFixture f;
  EXPECT_EQ(TextOfCondition("sel[5:2]", f), "sel[5:2]");
}

// §30.4.4.1 Table 30-1 lists the concatenation operator, so every operand of
// one has to appear, in the order the condition wrote them.
TEST(StateDependentPathConditionText, ConcatenationConditionNamesEveryElement) {
  SimFixture f;
  EXPECT_EQ(TextOfCondition("{gate, hold}", f), "{gate, hold}");
}

// §30.4.4.1 Table 30-1 lists the replication operator, so the repetition count
// and the operand it repeats both have to appear.
TEST(StateDependentPathConditionText,
     ReplicationConditionNamesCountAndElement) {
  SimFixture f;
  EXPECT_EQ(TextOfCondition("{4{gate}}", f), "{4{gate}}");
}

// §30.4.4.1 Table 30-1 lists the conditional operator, so the test and both
// arms have to appear, each in its own place.
TEST(StateDependentPathConditionText,
     ConditionalOperatorConditionNamesAllThreeOperands) {
  SimFixture f;
  EXPECT_EQ(TextOfCondition("hold ? gate : keep", f), "hold ? gate : keep");
}

// §32.4.1 matches a conditional entry on the condition, and the two sides write
// one part-select condition two ways: JoinSdfCondTokens rejoins the SDF side
// around the ':' NextSdfToken lexed on its own, where SpecifyConditionText
// writes no space there. This is the reading issue #3400 names: compared as
// strings the pair is unequal, so no SDF COND naming a part-select could reach
// the path that declared it.
TEST(StateDependentPathConditionSpelling,
     APartSelectSpelledWithAndWithoutSpacesIsOneCondition) {
  EXPECT_TRUE(SpecifyConditionsMatch("mode[7 : 6]", "mode[7:6]"));
}

// §32.4.1: whitespace is the only difference the comparison may overlook. Two
// conditions naming different bits of one vector are different conditions, and
// an entry written for one may not land on the other.
TEST(StateDependentPathConditionSpelling,
     ConditionsDifferingBeyondWhitespaceAreNotOneCondition) {
  EXPECT_FALSE(SpecifyConditionsMatch("mode[9 : 6]", "mode[7:6]"));
}

// Two state-dependent paths between one pair of terminals, told apart by
// nothing but which bit of `mode` each tests. §30.4.1 has the source of a
// module path be a net connected to an input port and the destination a net
// connected to an output port, which src_a and dst_y are.
const char* const kTwoBitConditions =
    "module path_cond_cell(input src_a, input [3:0] mode, output dst_y);\n"
    "  specify\n"
    "    if (mode[3]) (src_a => dst_y) = 37;\n"
    "    if (mode[1]) (src_a => dst_y) = 41;\n"
    "  endspecify\n"
    "endmodule\n";

// Two more paths between one pair of terminals, carrying the two condition
// forms whose SDF spelling crosses a token boundary: a part-select, which an
// SDF file lexes into three tokens, and a concatenation, which it lexes into
// one token or two according to the space after the comma. src_a and dst_y
// stand in the same §30.4.1 relation to the path as they do above.
const char* const kSpelledConditions =
    "module path_spell_cell(input src_a, input [7:0] mode, input en_hi,\n"
    "                       input en_lo, output dst_y);\n"
    "  specify\n"
    "    if (mode[7:6]) (src_a => dst_y) = 29;\n"
    "    if ({en_hi, en_lo}) (src_a => dst_y) = 23;\n"
    "  endspecify\n"
    "endmodule\n";

// Runs `src` and registers the module paths its last module declares onto
// `mgr` through BuildPathDelayFromDecl, which is the builder that asks
// SpecifyConditionText for each path's condition text.
bool RegisterPathsOf(const char* src, SimFixture& f, SpecifyManager& mgr) {
  auto* cu = RunModuleSource(src, f);
  if (cu == nullptr) return false;
  RegisterPathDelays(*cu->modules.back(), f, mgr);
  return true;
}

// Parses `sdf` and applies it to `mgr`.
void ApplySdfOnto(const std::string& sdf, SpecifyManager& mgr) {
  SdfFile file;
  ASSERT_TRUE(ParseSdf(sdf, file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);
}

// One DELAY-section entry inside the CELL record a DELAYFILE needs, naming the
// module `cell_type` is the name of.
std::string CellDelaySdf(const std::string& cell_type,
                         const std::string& entry) {
  return "(DELAYFILE (CELL (CELLTYPE \"" + cell_type +
         "\") (INSTANCE u_dut) (DELAY (ABSOLUTE " + entry + "))))";
}

// The registered path carrying `condition`, or null when none carries it. Both
// paths of each design above run between the same two terminals, so the
// condition alone is what tells them apart -- which is the whole of what
// §32.4.1 has left to match a conditional entry on once the ports agree.
// Backannotation leaves a path carrying the spelling the SDF file used, so the
// two are compared here the way §32.4.1 compares them.
const PathDelay* PathConditionedOn(const SpecifyManager& mgr,
                                   std::string_view condition) {
  for (const auto& pd : mgr.GetPathDelays()) {
    if (SpecifyConditionsMatch(pd.condition, condition)) return &pd;
  }
  return nullptr;
}

// Registers kSpelledConditions onto `mgr`, annotates `sdf_entry` onto it, and
// answers with the path carrying `condition` afterwards, which is the whole of
// what a case about one SDF spelling does.
const PathDelay* AnnotatedSpelledPath(SimFixture& f, SpecifyManager& mgr,
                                      const std::string& sdf_entry,
                                      std::string_view condition) {
  if (!RegisterPathsOf(kSpelledConditions, f, mgr)) return nullptr;
  ApplySdfOnto(CellDelaySdf("path_spell_cell", sdf_entry), mgr);
  return PathConditionedOn(mgr, condition);
}

// §32.4.1: a COND entry lands on the path declared under the same condition,
// so a condition written as a bit-select has to reach the path that declared
// it. This is the reading issue #3394 names: with the condition rendering to
// nothing, no COND text could equal it and the path kept its declared 37.
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

// §32.4.1: that entry lands on that path *only*, so the path testing another
// bit of the same vector keeps the 41 it was declared with. A condition text
// that named the vector without its bit would make the two paths agree, and
// the entry would reach whichever of them the annotator compared first.
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

// §32.4.1: a COND naming a part-select lands on the path declared under that
// part-select, so the declared 29 gives way to the file's 61. This is what
// issue #3400 costs: the file writes `mode[7:6]` and the SDF reader hands the
// comparison `mode[7 : 6]`, so string equality left the record nowhere and said
// nothing about it.
TEST(StateDependentPathConditionSpelling,
     SdfCondOnAPartSelectAnnotatesTheDeclaredPath) {
  SimFixture f;
  SpecifyManager mgr;

  const PathDelay* selected = AnnotatedSpelledPath(
      f, mgr, "(COND mode[7:6] (IOPATH src_a dst_y (61)))", "mode[7:6]");

  ASSERT_NE(selected, nullptr);
  EXPECT_EQ(selected->delays[0], 61u);
}

// §32.4.1: a COND naming a concatenation with no space after its comma lands on
// the path declared under that concatenation, so the declared 23 gives way to
// the file's 59. LexIdent runs `{en_hi,en_lo}` together into one token, where
// SpecifyConditionText writes the space Table 30-1's operator gets.
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

// §32.4.1 says nothing about how an SDF file spaces a condition, so the same
// concatenation written with a space after its comma lands on the same path,
// carrying the file's 67 over the declared 23. Written that way the reader
// makes two tokens of it rather than one.
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

}  // namespace

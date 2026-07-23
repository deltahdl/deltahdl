#include <string>
#include <vector>

// Completes the CoverageDB type that sim_context.h only forward-declares;
// included ahead of the fixtures so SimContext's inline constructor (whose
// unwind path destroys the owned coverage database) is well-formed in this TU.
#include "fixture_simulator.h"
#include "fixture_vcd.h"
#include "simulator/coverage.h"
#include "simulator/lowerer.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

// §21.7.2.2: the format of dumped variable values. Scalars and vectors each
// have their own record shape, scalar records abut the identifier code with no
// white space, vector records abut the base letter and separate the digits
// from the identifier code with one space, values are right-justified and
// shortened by dropping redundant left-extension digits (Tables 21-8/21-9),
// and an event is recorded as a scalar-format marker whose presence -- not its
// value character -- says the event triggered during the time step. Every
// rule governs a record whose value is produced by a declaration and its
// assignments, so the primary tests drive real SystemVerilog source through
// parse, elaboration, lowering, and the scheduler with the driver's
// per-timestep recording loop installed, then inspect the dump file.
class VcdValueFormatE2E : public VcdTestBase {
 protected:
  // Runs a single-module source through the full pipeline with the driver's
  // dump loop (timestamp + changed values at the end of each time unit) and
  // returns the dump file contents, mirroring the driver's registration
  // sequence (header, module scope, one registration per model variable,
  // $enddefinitions). Identifier codes ascend from '!' in name order.
  std::string RunVcd(const std::string& src) {
    SimFixture f;
    auto* design = ElaborateSrc(src, f);
    if (design == nullptr) return "<elaboration-failed>";
    Lowerer lowerer(f.ctx, f.arena, f.diag);
    lowerer.Lower(design);
    {
      VcdWriter vcd(tmp_path_);
      vcd.WriteHeader("1ns");
      vcd.BeginScope("t");
      f.ctx.RegisterVcdSignals(vcd);
      vcd.EndScope();
      vcd.EndDefinitions();
      // Value change dumping starts once the source's $dumpvars executes.
      vcd.ArmDumpvarsStart();
      f.ctx.SetVcdWriter(&vcd);
      f.scheduler.SetPostTimestepCallback([&vcd, &f]() {
        vcd.WriteTimestamp(f.ctx.CurrentTime().ticks);
        vcd.DumpChangedValues(0);
      });
      f.scheduler.Run();
    }  // writer destructor flushes the dump to tmp_path_ before ReadVcd
    return ReadVcd();
  }
};

std::vector<std::string> Lines(const std::string& content) {
  std::vector<std::string> out;
  std::string cur;
  for (char c : content) {
    if (c == '\n') {
      out.push_back(cur);
      cur.clear();
    } else {
      cur.push_back(c);
    }
  }
  if (!cur.empty()) out.push_back(cur);
  return out;
}

bool HasLine(const std::vector<std::string>& lines, std::string_view target) {
  for (const auto& l : lines) {
    if (l == target) return true;
  }
  return false;
}

size_t CountLine(const std::vector<std::string>& lines,
                 std::string_view target) {
  size_t n = 0;
  for (const auto& l : lines) {
    if (l == target) ++n;
  }
  return n;
}

// The portion of the file holding the simulation commands (value changes and
// timestamps). Substring negatives are checked here rather than in the whole
// file because a header $var line legitimately contains sequences such as
// "1 !" (its size and identifier code fields are space-separated).
std::string SimRegion(const std::string& content) {
  size_t pos = content.find("$enddefinitions");
  return pos == std::string::npos ? content : content.substr(pos);
}

// C1 + C2 (shall): a scalar variable declared in real source is dumped in the
// scalar format for each of its four states, with the value character abutting
// the identifier code. The declaration produces a 1-bit variable and the
// procedural assignments produce every admissible scalar value, so the test
// covers all four value characters, not just the 0/1 pair.
TEST_F(VcdValueFormatE2E, ScalarFourStatesAbutIdentifierCode) {
  auto content = RunVcd(
      "module t;\n"
      "  logic s;\n"
      "  initial begin\n"
      "    s = 1'b0;\n"
      "    $dumpvars;\n"
      "    #1 s = 1'b1;\n"
      "    #1 s = 1'bx;\n"
      "    #1 s = 1'bz;\n"
      "  end\n"
      "endmodule\n");
  auto lines = Lines(content);
  EXPECT_TRUE(HasLine(lines, "0!"));
  EXPECT_TRUE(HasLine(lines, "1!"));
  EXPECT_TRUE(HasLine(lines, "x!"));
  EXPECT_TRUE(HasLine(lines, "z!"));
  // NEGATIVE (C2): the spaced form a column-aligned writer might emit.
  auto sim = SimRegion(content);
  EXPECT_EQ(sim.find("0 !"), std::string::npos);
  EXPECT_EQ(sim.find("1 !"), std::string::npos);
  // NEGATIVE (C1): a scalar is never dumped in the vector b-format.
  for (const auto& l : lines) {
    EXPECT_TRUE(l.empty() || l[0] != 'b') << "scalar dumped as vector: " << l;
  }
}

// C1 + C3 (shall): a vector variable keeps the vector format even when its
// value shortens to a single digit -- the base letter b is present, abuts the
// digits, and exactly one space separates the digits from the identifier code.
TEST_F(VcdValueFormatE2E, VectorSingleDigitKeepsBaseLetterAndSpacing) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    v = 4'b0000;\n"
      "    $dumpvars;\n"
      "  end\n"
      "endmodule\n");
  auto lines = Lines(content);
  EXPECT_TRUE(HasLine(lines, "b0 !"));
  // NEGATIVE (C1): the vector must not degrade to the scalar format.
  EXPECT_FALSE(HasLine(lines, "0!"));
  // NEGATIVE (C3): no space may separate the base letter from the digits.
  EXPECT_EQ(content.find("b 0"), std::string::npos);
}

// C4 + C5 + C6 + C7: the four rows of Table 21-9 driven through a real 4-bit
// variable. Each assignment produces one full-width value whose dump must be
// the table's shortest form: redundant leading zeros drop entirely (row 1),
// runs of leading x or z collapse to a single digit because x extends with x
// and z with z (rows 2 and 3), and a 0 ahead of an x is retained because
// dropping it would left-extend the value with x rather than 0 (row 4). The
// checkpoint value of all ones additionally shows a leading 1 is never
// redundant (1 extends with 0), so no digits are dropped there.
TEST_F(VcdValueFormatE2E, ShortensOnlyRedundantFillDigits) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    v = 4'b1111;\n"
      "    $dumpvars;\n"
      "    #1 v = 4'b0010;\n"
      "    #1 v = 4'bxx10;\n"
      "    #1 v = 4'bzzx0;\n"
      "    #1 v = 4'b0x10;\n"
      "  end\n"
      "endmodule\n");
  auto lines = Lines(content);
  EXPECT_TRUE(HasLine(lines, "b1111 !"));
  EXPECT_TRUE(HasLine(lines, "b10 !"));
  EXPECT_TRUE(HasLine(lines, "bx10 !"));
  EXPECT_TRUE(HasLine(lines, "bzx0 !"));
  EXPECT_TRUE(HasLine(lines, "b0x10 !"));
  // NEGATIVE (C5): the full-width forms with their redundant digits.
  EXPECT_EQ(content.find("b0010"), std::string::npos);
  EXPECT_EQ(content.find("bxx10"), std::string::npos);
  EXPECT_EQ(content.find("bzzx0"), std::string::npos);
}

// C4: the retained digits are the low-order bits of the value -- shortening
// removes high-order redundancy only, so the record is right-justified. An
// 8-bit value of 00000110 must appear as b110; a left-anchored reading would
// keep 011 instead.
TEST_F(VcdValueFormatE2E, RightJustifiedRetainsLowOrderBits) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] v;\n"
      "  initial begin\n"
      "    v = 8'b00000110;\n"
      "    $dumpvars;\n"
      "  end\n"
      "endmodule\n");
  auto lines = Lines(content);
  EXPECT_TRUE(HasLine(lines, "b110 !"));
  EXPECT_FALSE(HasLine(lines, "b011 !"));
}

// C5/C6 at multi-word width: a declaration wider than one storage word still
// shortens across the word boundary. The 70-bit declaration starts all x
// (collapsing to bx) and the assignment of 5 collapses to b101, with none of
// the eliminated high-word zeros surviving.
TEST_F(VcdValueFormatE2E, WideVectorShortensAcrossStorageWords) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [69:0] w;\n"
      "  initial begin\n"
      "    $dumpvars;\n"
      "    #1 w = 70'd5;\n"
      "  end\n"
      "endmodule\n");
  auto lines = Lines(content);
  EXPECT_TRUE(HasLine(lines, "bx !"));
  EXPECT_TRUE(HasLine(lines, "b101 !"));
  EXPECT_EQ(content.find("b0101"), std::string::npos);
}

// C3 (shall) applied to the r-form of vector_value_change: a real variable's
// record likewise separates the number from the identifier code with exactly
// one space, and the base letter r abuts the number. (The number's %.16g
// rendering itself is §21.7.2's rule; only the spacing is observed here.)
TEST_F(VcdValueFormatE2E, RealRecordSpacingMatchesVectorRule) {
  auto content = RunVcd(
      "module t;\n"
      "  real r;\n"
      "  initial begin\n"
      "    r = 0.0;\n"
      "    $dumpvars;\n"
      "    #1 r = 0.5;\n"
      "  end\n"
      "endmodule\n");
  auto lines = Lines(content);
  EXPECT_TRUE(HasLine(lines, "r0 !"));
  EXPECT_TRUE(HasLine(lines, "r0.5 !"));
  EXPECT_EQ(content.find("r 0.5"), std::string::npos);
}

// C1 + C2 + C3 + C5 with the value produced by a declaration initializer
// rather than a procedural assignment: the format rules apply to the value
// however it was produced, so a scalar initialized at its declaration dumps in
// the scalar format and an initialized vector dumps in its shortened vector
// format at the $dumpvars checkpoint. Name order assigns s the code ! and v
// the code ".
TEST_F(VcdValueFormatE2E, DeclarationInitializerValuesUseSameFormats) {
  auto content = RunVcd(
      "module t;\n"
      "  logic s = 1'b1;\n"
      "  logic [3:0] v = 4'b0010;\n"
      "  initial $dumpvars;\n"
      "endmodule\n");
  auto lines = Lines(content);
  EXPECT_TRUE(HasLine(lines, "1!"));
  EXPECT_TRUE(HasLine(lines, "b10 \""));
  // The initializer-produced vector value shortens exactly like an assigned
  // one; its full-width form must not leak into the file.
  EXPECT_EQ(SimRegion(content).find("b0010"), std::string::npos);
}

// C1 + C3 + C5 over a 2-state element type: a bit vector reaches the writer
// through the 2-state storage path, yet its dump uses the same vector format
// and the same shortest-form elimination as a 4-state logic vector -- only 0
// and 1 digits can appear, and the redundant leading zeros still drop.
TEST_F(VcdValueFormatE2E, TwoStateVectorSharesVectorFormatAndShortening) {
  auto content = RunVcd(
      "module t;\n"
      "  bit [7:0] b;\n"
      "  initial begin\n"
      "    b = 8'b00000000;\n"
      "    $dumpvars;\n"
      "    #1 b = 8'b00001010;\n"
      "  end\n"
      "endmodule\n");
  auto lines = Lines(content);
  EXPECT_TRUE(HasLine(lines, "b0 !"));
  EXPECT_TRUE(HasLine(lines, "b1010 !"));
  // NEGATIVE (C5): the full-width form must not appear.
  EXPECT_EQ(SimRegion(content).find("b00001010"), std::string::npos);
}

// C1 + C4 + C5 over the predefined integer type: a 32-bit integer is a vector
// variable, so it dumps in the b-format with its value right-justified and
// shortened, exactly as an explicitly ranged declaration would.
TEST_F(VcdValueFormatE2E, IntegerVariableDumpsAsShortenedVector) {
  auto content = RunVcd(
      "module t;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    i = 0;\n"
      "    $dumpvars;\n"
      "    #1 i = 5;\n"
      "  end\n"
      "endmodule\n");
  auto lines = Lines(content);
  EXPECT_TRUE(HasLine(lines, "b0 !"));
  EXPECT_TRUE(HasLine(lines, "b101 !"));
  // NEGATIVE (C1): the integer must not degrade to the scalar format.
  EXPECT_FALSE(HasLine(lines, "0!"));
}

// C2 + C5 with the value produced by a nonblocking assignment: the NBA commit
// path delivers the value into the same records -- scalar abutting its code,
// vector shortened -- as a blocking assignment does, so the format rules do
// not depend on which assignment flavor produced the value.
TEST_F(VcdValueFormatE2E, NonblockingAssignmentProducesSameFormats) {
  auto content = RunVcd(
      "module t;\n"
      "  logic s;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    s = 1'b0;\n"
      "    v = 4'b0000;\n"
      "    $dumpvars;\n"
      "    #1 begin s <= 1'b1; v <= 4'b0010; end\n"
      "  end\n"
      "endmodule\n");
  auto lines = Lines(content);
  EXPECT_TRUE(HasLine(lines, "1!"));
  EXPECT_TRUE(HasLine(lines, "b10 \""));
  auto sim = SimRegion(content);
  EXPECT_EQ(sim.find("1 !"), std::string::npos);
  EXPECT_EQ(sim.find("b0010"), std::string::npos);
}

// C8: a named event declared in real source and fired by a trigger statement
// is dumped in the scalar format -- value abutting the identifier code -- and
// the record appears exactly once, in the time step of the trigger, as a
// marker. In every other time step (including the $dumpvars checkpoint, where
// the event holds no meaningful value) the event contributes nothing.
TEST_F(VcdValueFormatE2E, EventTriggerDumpsScalarFormatMarker) {
  // Name order assigns clk the code ! and ev the code ".
  auto content = RunVcd(
      "module t;\n"
      "  event ev;\n"
      "  logic clk;\n"
      "  initial begin\n"
      "    clk = 1'b0;\n"
      "    $dumpvars;\n"
      "    #5 -> ev;\n"
      "    #5 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  auto lines = Lines(content);
  // The marker appears exactly once: the trigger's time step and no other.
  EXPECT_EQ(CountLine(lines, "1\""), 1u);
  // The marker lands in the #5 section, after that timestamp and before #10.
  size_t at_trigger = content.find("#5\n1\"");
  EXPECT_NE(at_trigger, std::string::npos);
  // NEGATIVE: an untriggered event is never dumped -- no checkpoint value, no
  // 0-valued record, no x record from the initial time steps.
  EXPECT_FALSE(HasLine(lines, "0\""));
  EXPECT_FALSE(HasLine(lines, "x\""));
  // Scalar-format rule holds for the marker: no white space before the code.
  EXPECT_EQ(SimRegion(content).find("1 \""), std::string::npos);
}

}  // namespace
}  // namespace delta

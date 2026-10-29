#include <gtest/gtest.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <format>
#include <span>
#include <string>
#include <string_view>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §6.23 (printed page 138): a type reference to an expression stands for the
// expression's self-determined type, the expression left unevaluated, and two
// type references compared with ==, !=, === or !== give whether the two types
// match (§6.22.1). Each comparison below holds against the type its operand
// has by §11.6.1's widths, §11.8.1's signing, §11.3.1's real operands and
// §11.3.4's 2- and 4-state operands, or fails against the type nearest it.
struct Comparison {
  const char* text;
  bool holds;
};

// The operands every comparison reads.
constexpr const char* kOperands =
    "  byte a;\n"
    "  bit [7:0] b;\n"
    "  logic [3:0] c;\n"
    "  shortint s;\n"
    "  logic [7:0] v;\n"
    "  logic signed [7:0] sv;\n"
    "  logic [3:0][7:0] pk;\n"
    "  int i;\n"
    "  logic [5:0] x;\n"
    "  real rl;\n"
    "  shortreal srl;\n"
    "  bit flag;\n"
    "  typedef struct packed { byte f; logic [2:0] g; } ps_t;\n"
    "  ps_t p;\n"
    "  bit [5:0] arr [4];\n"
    "  typedef enum {E0, E1} e_t;\n"
    "  localparam byte P = 3;\n";

// §11.6.1 with §11.8.1: an arithmetic operator is as wide as its wider
// operand, signed where both are and 4-state where either is; a unary minus
// is its operand's type.
constexpr std::array kArithmetic = {
    Comparison{"type(a + b) == type(bit [7:0])", true},
    Comparison{"type(a + b) == type(byte)", false},
    Comparison{"type(a + s) == type(shortint)", true},
    Comparison{"type(a + s) == type(bit [15:0])", false},
    Comparison{"type(a + c) == type(logic [7:0])", true},
    Comparison{"type(a + c) == type(bit [7:0])", false},
    Comparison{"type(-a) == type(byte)", true},
    Comparison{"type(-a) == type(bit [7:0])", false},
    Comparison{"type(a + b) == type(b + a)", true},
    Comparison{"type(a + b) != type(a + c)", true},
};

// §11.6.1: a bitwise operator sizes as an arithmetic one does, and a shift is
// its left operand's type, 4-state where either operand is.
constexpr std::array kBitwiseAndShift = {
    Comparison{"type(a & b) == type(bit [7:0])", true},
    Comparison{"type(a & c) == type(bit [7:0])", false},
    Comparison{"type(a << b) == type(byte)", true},
    Comparison{"type(a << b) == type(bit [7:0])", false},
    Comparison{"type(a >>> c) == type(logic signed [7:0])", true},
    Comparison{"type(a >>> c) == type(byte)", false},
};

// §11.6.1 with §11.8.1: a relational, equality, logical, reduction or
// set membership operator is one unsigned bit.
constexpr std::array kOneBitResults = {
    Comparison{"type(a < b) == type(bit)", true},
    Comparison{"type(a < b) == type(logic)", false},
    Comparison{"type(a == c) == type(logic)", true},
    Comparison{"type(a == c) == type(bit)", false},
    Comparison{"type(a && b) == type(bit)", true},
    Comparison{"type(a && b) == type(bit [7:0])", false},
    Comparison{"type(&b) == type(bit)", true},
    Comparison{"type(!c) == type(logic)", true},
    Comparison{"type(b inside {a, b}) == type(bit)", true},
    Comparison{"type(c inside {a}) == type(bit)", false},
};

// §11.5.1 with §11.8.1 and §7.4.1: a bit-select is one bit and a part-select
// as many bits as it names, unsigned and of the vector's state; an element of
// a packed array is the array's element type.
constexpr std::array kSelects = {
    Comparison{"type(v[3]) == type(logic)", true},
    Comparison{"type(v[3]) == type(bit)", false},
    Comparison{"type(v[7:4]) == type(logic [3:0])", true},
    Comparison{"type(v[7:4]) == type(logic [4:0])", false},
    Comparison{"type(sv[i +: 4]) == type(logic [3:0])", true},
    Comparison{"type(sv[i +: 4]) == type(logic signed [3:0])", false},
    Comparison{"type(sv[7 -: 3]) == type(logic [2:0])", true},
    Comparison{"type(pk[1]) == type(logic [7:0])", true},
    Comparison{"type(pk[1]) == type(logic [31:0])", false},
    Comparison{"type(pk[2:1]) == type(logic [15:0])", true},
};

// §7.2 and §7.4.2: a member of a structure is the type it was declared with,
// and an element of an unpacked array the array's element type.
constexpr std::array kMembersAndElements = {
    Comparison{"type(p.g) == type(logic [2:0])", true},
    Comparison{"type(p.g) == type(bit [2:0])", false},
    Comparison{"type(p.f) == type(byte)", true},
    Comparison{"type(p.f) == type(bit [7:0])", false},
    Comparison{"type(p.f[0]) == type(bit)", true},
    Comparison{"type(arr[1]) == type(bit [5:0])", true},
    Comparison{"type(arr[1]) == type(bit [4:0])", false},
    Comparison{"type(arr[1][2]) == type(bit)", true},
};

// §11.4.12 and §11.4.12.1: a concatenation is unsigned and as wide as its
// operands together, a replication its count of copies of them; §11.4.11: a
// conditional is as wide as its wider result, signed where both are and
// 4-state where its condition or a result is.
constexpr std::array kConcatenationsAndConditionals = {
    Comparison{"type({a, b}) == type(bit [15:0])", true},
    Comparison{"type({a, b}) == type(shortint)", false},
    Comparison{"type({2{c}}) == type(logic [7:0])", true},
    Comparison{"type({2{c}}) == type(logic [3:0])", false},
    Comparison{"type({a, c}) == type(logic [11:0])", true},
    Comparison{"type(flag ? a : b) == type(bit [7:0])", true},
    Comparison{"type(flag ? a : b) == type(byte)", false},
    Comparison{"type(flag ? a : s) == type(shortint)", true},
    Comparison{"type(c[0] ? a : b) == type(logic [7:0])", true},
};

// §6.24.1: a cast is the type it names, a signing cast its operand with the
// signing it names, and a size cast its operand's signing and state at the
// size it names.
constexpr std::array kCasts = {
    Comparison{"type(byte'(b)) == type(byte)", true},
    Comparison{"type(byte'(b)) == type(bit [7:0])", false},
    Comparison{"type(signed'(v)) == type(logic signed [7:0])", true},
    Comparison{"type(signed'(v)) == type(logic [7:0])", false},
    Comparison{"type(unsigned'(a)) == type(bit [7:0])", true},
    Comparison{"type(4'(b)) == type(bit [3:0])", true},
    Comparison{"type(4'(a)) == type(bit signed [3:0])", true},
    Comparison{"type(e_t'(i)) == type(e_t)", true},
    Comparison{"type(e_t'(i)) == type(int)", false},
    Comparison{"type(type(c)'(b)) == type(logic [3:0])", true},
};

// §11.4.2 and §11.3.6: an increment, a decrement and an assignment are the
// type of the variable they would change, with none of them carried out.
constexpr std::array kIncrementsAndAssignments = {
    Comparison{"type(i++) == type(int)", true},
    Comparison{"type(i++) == type(integer)", false},
    Comparison{"type(--i) == type(int)", true},
    Comparison{"type((x += 3)) == type(logic [5:0])", true},
    Comparison{"type((x += 3)) == type(logic [6:0])", false},
    Comparison{"type((x = b)) == type(logic [5:0])", true},
};

// A system function is the type its clause gives its result: an integer for
// $bits (§20.6.2) and $clog2 (§20.8.1), an int for $countones (§20.9), a bit
// for $isunknown (§20.9) and a real for $itor (§20.5); $signed and $unsigned
// (§11.7) are their argument with the signing each names.
constexpr std::array kSystemFunctions = {
    Comparison{"type($bits(x)) == type(integer)", true},
    Comparison{"type($bits(x)) == type(int)", false},
    Comparison{"type($clog2(8)) == type(integer)", true},
    Comparison{"type($signed(v)) == type(logic signed [7:0])", true},
    Comparison{"type($signed(v)) == type(logic [7:0])", false},
    Comparison{"type($unsigned(a)) == type(bit [7:0])", true},
    Comparison{"type($countones(v)) == type(int)", true},
    Comparison{"type($isunknown(v)) == type(bit)", true},
    Comparison{"type($itor(i)) == type(real)", true},
};

// §5.7.1: an integer literal is as wide as its size, or 32 bits unsized,
// signed where it is decimal or carries the s designator, and 4-state; an
// unbased unsized literal is one bit where it is self-determined. §5.7.2 and
// §5.8: a real or time literal is real. §5.9: a string literal is an unsigned
// integral value of eight bits a character.
constexpr std::array kLiterals = {
    Comparison{"type(4'b1010) == type(logic [3:0])", true},
    Comparison{"type(4'b1010) == type(bit [3:0])", false},
    Comparison{"type(-4'sd3) == type(logic signed [3:0])", true},
    Comparison{"type(-4'sd3) == type(logic [3:0])", false},
    Comparison{"type(5) == type(integer)", true},
    Comparison{"type(5) == type(int)", false},
    Comparison{"type('1) == type(logic)", true},
    Comparison{"type(1.5) == type(real)", true},
    Comparison{"type(1.5) == type(shortreal)", false},
    Comparison{"type(1ns) == type(real)", true},
    Comparison{"type(\"ab\") == type(logic [15:0])", true},
    Comparison{"type(\"ab\") == type(logic [7:0])", false},
};

// §11.3.1: an operator with a real operand is real, and one with a shortreal
// operand and no real one is shortreal.
constexpr std::array kRealOperands = {
    Comparison{"type(rl * 2) == type(real)", true},
    Comparison{"type(srl + b) == type(shortreal)", true},
    Comparison{"type(srl + b) == type(real)", false},
    Comparison{"type(srl + rl) == type(real)", true},
    Comparison{"type(rl ** 2) == type(real)", true},
    Comparison{"type(flag ? rl : a) == type(real)", true},
};

// §6.20.2 and §6.19.3: a parameter is the type it was declared with, and an
// enumeration's named constant is of the enumeration's type.
constexpr std::array kParametersAndConstants = {
    Comparison{"type(P) == type(byte)", true},
    Comparison{"type(P) == type(bit [7:0])", false},
    Comparison{"type(P + b) == type(bit [7:0])", true},
    Comparison{"type(E1) == type(e_t)", true},
    Comparison{"type(E1) == type(int)", false},
};

struct ComparisonGroup {
  const char* name;
  std::span<const Comparison> comparisons;
  // §11.3.6 (printed page 275): an assignment operator stands only in an
  // expression within a procedural statement, a type reference's included.
  bool procedural_only = false;
};

constexpr std::array kGroups = {
    ComparisonGroup{"arithmetic", kArithmetic},
    ComparisonGroup{"bitwise and shift", kBitwiseAndShift},
    ComparisonGroup{"one-bit results", kOneBitResults},
    ComparisonGroup{"selects", kSelects},
    ComparisonGroup{"members and elements", kMembersAndElements},
    ComparisonGroup{"concatenations and conditionals",
                    kConcatenationsAndConditionals},
    ComparisonGroup{"casts", kCasts},
    ComparisonGroup{"increments and assignments", kIncrementsAndAssignments,
                    true},
    ComparisonGroup{"system functions", kSystemFunctions},
    ComparisonGroup{"literals", kLiterals},
    ComparisonGroup{"real operands", kRealOperands},
    ComparisonGroup{"parameters and constants", kParametersAndConstants},
};

// Where §6.23 lets a comparison of type references stand: a procedural if's
// condition, a continuous assignment's right-hand side, a generate if's
// condition (§27.5) and a localparam's value (§6.20.4).
enum class Place : std::uint8_t {
  kProceduralIf,
  kContinuousAssignment,
  kGenerateIf,
  kParam
};

// A module declaring the operands and writing each comparison of `group` at
// `place`, the k-th setting the bit of r k places below its most significant.
std::string ModuleComparing(std::span<const Comparison> group, Place place) {
  const size_t kCount = group.size();
  std::string src =
      std::format("module t;\n{}  bit [{}:0] r;\n", kOperands, kCount - 1);
  std::string listed;
  std::string body;
  for (size_t k = 0; k < kCount; ++k) {
    const std::string_view kText = group[k].text;
    const std::string kBit = std::format("r[{}]", kCount - 1 - k);
    const std::string_view kSeparator = k == 0 ? "" : ", ";
    switch (place) {
      case Place::kProceduralIf:
        body += std::format("    if ({}) {} = 1'b1;\n", kText, kBit);
        break;
      case Place::kContinuousAssignment:
        listed += std::format("{}{}", kSeparator, kText);
        break;
      case Place::kGenerateIf:
        src += std::format(
            "  if ({0}) begin : g{1} initial {2} = 1'b1; end\n"
            "  else begin : h{1} initial {2} = 1'b0; end\n",
            kText, k, kBit);
        break;
      default:
        src += std::format("  localparam bit L{} = {};\n", k, kText);
        listed += std::format("{}L{}", kSeparator, k);
        break;
    }
  }
  if (place == Place::kProceduralIf)
    src += std::format("  initial begin\n{}  end\n", body);
  if (place == Place::kContinuousAssignment)
    src += std::format("  assign r = {{{}}};\n", listed);
  if (place == Place::kParam)
    src += std::format("  initial r = {{{}}};\n", listed);
  return src + "endmodule\n";
}

// The value r takes where each comparison of `group` gives what the standard
// says it gives.
uint64_t ExpectedBits(std::span<const Comparison> group) {
  uint64_t bits = 0;
  for (const Comparison& comparison : group) {
    bits = (bits << 1) | (comparison.holds ? 1u : 0u);
  }
  return bits;
}

void ExpectEveryGroupAt(Place place) {
  for (const ComparisonGroup& group : kGroups) {
    if (group.procedural_only && place != Place::kProceduralIf) continue;
    SCOPED_TRACE(group.name);
    EXPECT_EQ(RunAndGet(ModuleComparing(group.comparisons, place), "r"),
              ExpectedBits(group.comparisons));
  }
}

TEST(TypeOfExpressionCompareSim, ComparisonInAProceduralIf) {
  ExpectEveryGroupAt(Place::kProceduralIf);
}

TEST(TypeOfExpressionCompareSim, ComparisonInAContinuousAssignment) {
  ExpectEveryGroupAt(Place::kContinuousAssignment);
}

TEST(TypeOfExpressionCompareSim, ComparisonSelectsAGenerateBranch) {
  ExpectEveryGroupAt(Place::kGenerateIf);
}

TEST(TypeOfExpressionCompareSim, ComparisonSetsAParameter) {
  ExpectEveryGroupAt(Place::kParam);
}

// §6.23: the expression a type reference names is not evaluated, so neither
// the increment nor the operator assignment a comparison names changes the
// variable it would write.
TEST(TypeOfExpressionCompareSim, ComparedExpressionIsNotEvaluated) {
  const std::string kSrc =
      "module t;\n"
      "  int i = 5;\n"
      "  logic [5:0] x = 1;\n"
      "  bit [1:0] r;\n"
      "  initial r = {type(i++) == type(int), type((x += 3)) == type(int)};\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "r"), 0b10u);
  EXPECT_EQ(RunAndGet(kSrc, "i"), 5u);
  EXPECT_EQ(RunAndGet(kSrc, "x"), 1u);
}

// §6.23 with §27.5: a name in the expression is the value the generate block
// the comparison stands in declares, where the module declares another of the
// name.
TEST(TypeOfExpressionCompareSim, OperandOfAGenerateBlockIsTypedInTheBlock) {
  const std::string kSrc =
      "module t;\n"
      "  wire [7:0] n;\n"
      "  bit [2:0] r;\n"
      "  if (1) begin : g\n"
      "    wire [0:3] n;\n"
      "    initial r = {type(n[0:1]) == type(logic [1:0]),\n"
      "                 type(n + n) == type(logic [3:0]),\n"
      "                 type(n + n) == type(logic [7:0])};\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "r"), 0b110u);
}

// §6.23: a declaration whose type is a type reference to an expression takes
// the expression's self-determined type: 2-state where every operand is, so x
// assigned to it reads as 0, signed where every operand is, as wide as §11.6.1
// makes it, and real where an operand is.
TEST(TypeOfExpressionDeclarationSim, DeclarationTakesTheSelfDeterminedType) {
  const std::string kSrc =
      "module t;\n"
      "  byte a;\n"
      "  bit [7:0] b;\n"
      "  logic [3:0] c;\n"
      "  shortint s;\n"
      "  real rl;\n"
      "  var type(a + b) d;\n"
      "  var type(a + s) e;\n"
      "  var type(a + c) f;\n"
      "  var type({a, b}) h;\n"
      "  var type(rl * 2) g;\n"
      "  bit [18:0] r;\n"
      "  initial begin\n"
      "    d = 'x;\n"
      "    e = -1;\n"
      "    f = 'x;\n"
      "    h = 'x;\n"
      "    g = 1.25;\n"
      "    r = {$isunknown(d), e < 0, $isunknown(f), $isunknown(h),\n"
      "         5'($bits(d)), 5'($bits(e)), 5'($bits(h))};\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "r"), 0b0110'01000'10000'10000u);
  EXPECT_EQ(RunAndGetReal(kSrc, "g"), 1.25);
}

}  // namespace

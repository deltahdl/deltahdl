#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "fixture_vpi_run.h"
#include "simulator/variable.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class ExpressionValuesOfARun : public VpiDesignRun {
 protected:
  // The right side of the continuous assignment `scope` holds.
  static vpiHandle RhsIn(const char* scope) {
    vpiHandle it = vpi_iterate(vpiContAssign, By(scope));
    if (it == nullptr) return nullptr;
    return vpi_handle(vpiRhs, vpi_scan(it));
  }

  // The integer value of an object, or -1 where the routine fills none.
  static int IntOf(vpiHandle obj) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    value.value.integer = -1;
    vpi_get_value(obj, &value);
    return value.value.integer;
  }
};

// §38.15 with §37.3.5: an operation is an expression vpi_get_value can read,
// its value the expression evaluated, its names read where the source wrote
// them -- in the top, and in a child instance whose port names the same as a
// variable of the top. The operation held no storage and gave no value.
TEST_F(ExpressionValuesOfARun, AnOperationReadsAsItsExpressionEvaluates) {
  Run("module child(input logic [7:0] a); logic [7:0] b = 30;\n"
      "  wire [7:0] y; assign y = a + b;\n"
      "endmodule\n"
      "module top; logic [7:0] a = 5, b = 7; wire [7:0] y;\n"
      "  assign y = a + b; child u(.a(8'd1));\n"
      "endmodule\n");
  vpiHandle top = RhsIn("top");
  vpiHandle child = RhsIn("top.u");
  ASSERT_NE(top, nullptr);
  ASSERT_NE(child, nullptr);
  EXPECT_EQ(vpi_get(vpiType, top), vpiOperation);
  EXPECT_EQ(IntOf(top), 12);
  EXPECT_EQ(IntOf(child), 31);
}

// §37.17 detail 26 with §37.3.5: a select whose index is an operation stands
// for the element the operation's value names, m[2] for `m[i + 1]` with i 1,
// read and written alike. The index's value was taken from storage the
// operation does not have, so the select named no element: it read x and a
// put to it wrote nothing.
TEST_F(ExpressionValuesOfARun, ASelectIndexedByAnOperationNamesItsElement) {
  Run("module top; logic [3:0][7:0] m = 32'h44332211; integer i = 1;\n"
      "  wire [7:0] y; assign y = m[i + 1];\n"
      "endmodule\n");
  vpiHandle select = RhsIn("top");
  ASSERT_NE(select, nullptr);
  EXPECT_EQ(IntOf(select), 0x33);
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 0x55;
  vpi_put_value(select, &value, nullptr, vpiNoDelay);
  EXPECT_EQ(IntOf(By("top.m")), 0x44552211);
}

// §38.15 with §37.3.5: a function call and a system function call are
// expressions vpi_get_value reads by evaluating them, as is a select whose
// index is a call: f(5) is 10, $clog2(5) is 3, and m[f(i)] with f(1) 2 is
// m[2]. The calls held no storage and gave no value, and the select named no
// element.
TEST_F(ExpressionValuesOfARun, ACallReadsAsItsCallEvaluates) {
  Run("module top; logic [7:0] a = 5; logic [3:0][7:0] m = 32'h44332211;\n"
      "  integer i = 1; wire [7:0] y; wire [31:0] z; wire [7:0] w;\n"
      "  function automatic logic [7:0] f(input logic [7:0] x);\n"
      "    return x * 2;\n"
      "  endfunction\n"
      "  function automatic integer g(input integer x); return x + 1;\n"
      "  endfunction\n"
      "  assign y = f(a); assign z = $clog2(a); assign w = m[g(i)];\n"
      "endmodule\n");
  vpiHandle it = vpi_iterate(vpiContAssign, By("top"));
  ASSERT_NE(it, nullptr);
  vpiHandle call = vpi_handle(vpiRhs, vpi_scan(it));
  vpiHandle system_call = vpi_handle(vpiRhs, vpi_scan(it));
  vpiHandle select = vpi_handle(vpiRhs, vpi_scan(it));
  ASSERT_NE(call, nullptr);
  ASSERT_NE(system_call, nullptr);
  ASSERT_NE(select, nullptr);
  EXPECT_EQ(vpi_get(vpiType, call), vpiFuncCall);
  EXPECT_EQ(IntOf(call), 10);
  EXPECT_EQ(vpi_get(vpiType, system_call), vpiSysFuncCall);
  EXPECT_EQ(IntOf(system_call), 3);
  EXPECT_EQ(IntOf(select), 0x33);
}

// §11.5.1 with §37.17 detail 26: a select whose index holds x, or names no
// element of the dimension it indexes, selects nothing, and reads x in each of
// its bits out of a 4-state vector and 0 out of a 2-state one, all 64 of them
// for an element as wide as a word; a value put to it is written nowhere.
TEST_F(ExpressionValuesOfARun, ASelectNamingNoElementReadsItsVectorsDefault) {
  Run("module top; logic [3:0][7:0] m = 32'h44332211; integer i = 'x;\n"
      "  bit [3:0][7:0] b = 32'h44332211; integer j = 9;\n"
      "  logic [1:0][63:0] w = 0; integer k = 5;\n"
      "  wire [7:0] y, z; wire [63:0] v;\n"
      "  assign y = m[i]; assign z = b[j]; assign v = w[k];\n"
      "endmodule\n");
  vpiHandle it = vpi_iterate(vpiContAssign, By("top"));
  ASSERT_NE(it, nullptr);
  vpiHandle x_index = vpi_handle(vpiRhs, vpi_scan(it));
  vpiHandle two_state = vpi_handle(vpiRhs, vpi_scan(it));
  vpiHandle wide = vpi_handle(vpiRhs, vpi_scan(it));
  ASSERT_NE(x_index, nullptr);
  ASSERT_NE(two_state, nullptr);
  ASSERT_NE(wide, nullptr);
  s_vpi_value value = {};
  value.format = vpiBinStrVal;
  vpi_get_value(x_index, &value);
  EXPECT_STREQ(value.value.str, "xxxxxxxx");
  vpi_get_value(two_state, &value);
  EXPECT_STREQ(value.value.str, "00000000");
  vpi_get_value(wide, &value);
  EXPECT_EQ(std::string(value.value.str), std::string(64, 'x'));

  s_vpi_value put = {};
  put.format = vpiIntVal;
  put.value.integer = 0x55;
  EXPECT_EQ(vpi_put_value(x_index, &put, nullptr, vpiNoDelay), nullptr);
  EXPECT_EQ(IntOf(By("top.m")), 0x44332211);
}

// §27.4 with §37.17 detail 26: a select written in a loop generate block
// whose index is the loop's genvar stands for the element the genvar names in
// the block instance, m[2] for g 2. The loop makes one instance, a
// continuous assignment in a block being one VPI object for every instance
// of it (#5694).
TEST_F(ExpressionValuesOfARun, AGenvarIndexedSelectNamesItsBlocksElement) {
  Run("module top; logic [3:0][7:0] m = 32'h44332211;\n"
      "  for (genvar g = 2; g < 3; g++) begin : gb\n"
      "    wire [7:0] y; assign y = m[g];\n"
      "  end\n"
      "endmodule\n");
  vpiHandle select = RhsIn("top");
  ASSERT_NE(select, nullptr);
  EXPECT_EQ(IntOf(select), 0x33);
}

// Whether VpiPutValueBits takes a value of `format` whose text is `text` at
// `width`, the words it decodes it into left in `words`.
bool DecodesText(int format, std::string text, uint32_t width,
                 std::vector<Logic4Word>& words) {
  s_vpi_value value = {};
  value.format = format;
  value.value.str = text.data();
  return VpiPutValueBits(value, width, words);
}

// Whether VpiPutValueBits refuses a value of `format` whose text is `text`.
bool RefusesText(int format, std::string text) {
  std::vector<Logic4Word> words;
  return !DecodesText(format, std::move(text), 8, words);
}

// The low word a value of `format` whose text is `text` decodes into at
// `width`; all ones where it is refused.
uint64_t LowWordOfText(int format, std::string text, uint32_t width) {
  std::vector<Logic4Word> words;
  return DecodesText(format, std::move(text), width, words) ? words[0].aval
                                                            : ~uint64_t{0};
}

// Table 38-3 (vpiDecStrVal): a minus sign makes the number negative in two's
// complement across every word, the carry crossing into the next word where a
// word's negation is 0.
TEST(PutValueDecoding, ADecimalNegationCarriesAcrossWords) {
  std::vector<Logic4Word> words;
  ASSERT_TRUE(DecodesText(vpiDecStrVal, "-1", 128, words));
  EXPECT_EQ(words[0].aval, ~uint64_t{0});
  EXPECT_EQ(words[1].aval, ~uint64_t{0});
  ASSERT_TRUE(DecodesText(vpiDecStrVal, "-18446744073709551616", 128, words));
  EXPECT_EQ(words[0].aval, 0u);
  EXPECT_EQ(words[1].aval, ~uint64_t{0});
}

// Table 38-3 (vpiIntVal): a non-negative integer leaves the words above its
// own 0.
TEST(PutValueDecoding, APositiveIntegerLeavesTheHighWordsClear) {
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 5;
  std::vector<Logic4Word> words;
  ASSERT_TRUE(VpiPutValueBits(value, 128, words));
  EXPECT_EQ(words[0].aval, 5u);
  EXPECT_EQ(words[1].aval, 0u);
}

// Table 38-3: a character that is no digit of the format's base is refused,
// whether it is a digit of a larger base or no digit at all; and a decimal
// string must hold at least one digit.
TEST(PutValueDecoding, ACharacterOutsideTheBaseIsRefused) {
  EXPECT_TRUE(RefusesText(vpiBinStrVal, "2"));
  EXPECT_TRUE(RefusesText(vpiHexStrVal, "#"));
  EXPECT_TRUE(RefusesText(vpiHexStrVal, ":"));
  EXPECT_TRUE(RefusesText(vpiHexStrVal, "g"));
  EXPECT_TRUE(RefusesText(vpiDecStrVal, ""));
  EXPECT_TRUE(RefusesText(vpiDecStrVal, "-"));
  EXPECT_TRUE(RefusesText(vpiDecStrVal, "1#"));
  EXPECT_TRUE(RefusesText(vpiDecStrVal, "1a"));
}

// Table 38-3: digits and characters are taken from the right, and those past
// the object's width are dropped, a digit or character cut where the width
// ends inside it.
TEST(PutValueDecoding, TextPastTheWidthIsDropped) {
  EXPECT_EQ(LowWordOfText(vpiBinStrVal, "101", 2), 1u);
  EXPECT_EQ(LowWordOfText(vpiHexStrVal, "F", 2), 3u);
  EXPECT_EQ(LowWordOfText(vpiStringVal, "AB", 8), 0x42u);
  EXPECT_EQ(LowWordOfText(vpiStringVal, "A", 4), 0x1u);
}

// Figure 38-8: a scalar or a strength's logic value in bit 0 -- 0 as (0, 0),
// x as (1, 1) and z as (0, 1).
TEST(PutValueDecoding, ScalarAndStrengthLogicTakeTheirEncoding) {
  const struct {
    int scalar;
    uint64_t aval;
    uint64_t bval;
  } kCases[] = {{vpi0, 0, 0}, {vpiX, 1, 1}, {vpiZ, 0, 1}};
  std::vector<Logic4Word> words;
  for (const auto& c : kCases) {
    s_vpi_value value = {};
    value.format = vpiScalarVal;
    value.value.scalar = c.scalar;
    ASSERT_TRUE(VpiPutValueBits(value, 1, words)) << c.scalar;
    EXPECT_EQ(words[0].aval, c.aval) << c.scalar;
    EXPECT_EQ(words[0].bval, c.bval) << c.scalar;
  }
  s_vpi_strengthval strength = {};
  strength.logic = vpiZ;
  s_vpi_value value = {};
  value.format = vpiStrengthVal;
  value.value.strength = &strength;
  ASSERT_TRUE(VpiPutValueBits(value, 1, words));
  EXPECT_EQ(words[0].bval, 1u);
}

// A value whose pointer member is null, a zero width, and a format no put
// takes are refused.
TEST(PutValueDecoding, NullPointersZeroWidthAndOtherFormatsAreRefused) {
  std::vector<Logic4Word> words;
  for (int format : {vpiBinStrVal, vpiTimeVal, vpiVectorVal, vpiStrengthVal}) {
    s_vpi_value value = {};
    value.format = format;
    EXPECT_FALSE(VpiPutValueBits(value, 8, words)) << format;
  }
  s_vpi_value value = {};
  value.format = vpiIntVal;
  EXPECT_FALSE(VpiPutValueBits(value, 0, words));
  value.format = vpiObjTypeVal;
  EXPECT_FALSE(VpiPutValueBits(value, 8, words));
}

// A write that runs past the object's storage stops at its end.
TEST(PutValueDecoding, AWritePastTheStorageStopsAtItsEnd) {
  Arena arena;
  Variable storage;
  storage.value = MakeLogic4Vec(arena, 64);
  VpiObject obj;
  obj.var = &storage;
  obj.bit_offset = 60;
  const std::vector<Logic4Word> kOnes = {{0xFF, 0}};
  VpiWriteDecodedBits(obj, kOnes, 8);
  EXPECT_EQ(storage.value.words[0].aval, uint64_t{0xF} << 60);
}

}  // namespace
}  // namespace delta

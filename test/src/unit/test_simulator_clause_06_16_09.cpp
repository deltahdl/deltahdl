#include "builders_ast.h"
#include "fixture_string.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(StringMethods, Atoi) {
  StringFixture f;
  f.CreateStringVar("s", "42");
  auto* call = f.MakeMethodCall("s", "atoi");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(StringMethods, Atohex) {
  StringFixture f;
  f.CreateStringVar("s", "1f");
  auto* call = f.MakeMethodCall("s", "atohex");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0x1fu);
}

TEST(StringMethods, Atooct) {
  StringFixture f;
  f.CreateStringVar("s", "77");
  auto* call = f.MakeMethodCall("s", "atooct");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 077u);
}

TEST(StringMethods, Atobin) {
  StringFixture f;
  f.CreateStringVar("s", "1010");
  auto* call = f.MakeMethodCall("s", "atobin");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0b1010u);
}

TEST(StringMethods, AtoiNoDigitsReturnsZero) {
  StringFixture f;
  f.CreateStringVar("s", "abc");
  auto* call = f.MakeMethodCall("s", "atoi");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(StringMethods, AtoiEmptyStringReturnsZero) {
  StringFixture f;
  f.CreateStringVar("s", "");
  auto* call = f.MakeMethodCall("s", "atoi");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(StringMethods, AtoiStopsAtNonDigit) {
  StringFixture f;
  f.CreateStringVar("s", "123xyz");
  auto* call = f.MakeMethodCall("s", "atoi");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 123u);
}

TEST(StringMethods, AtohexNoDigitsReturnsZero) {
  StringFixture f;
  f.CreateStringVar("s", "xyz");
  auto* call = f.MakeMethodCall("s", "atohex");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(StringMethods, AtobinNoDigitsReturnsZero) {
  StringFixture f;
  f.CreateStringVar("s", "xyz");
  auto* call = f.MakeMethodCall("s", "atobin");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(StringMethods, AtoiReturns32Bit) {
  StringFixture f;
  f.CreateStringVar("s", "100");
  auto* call = f.MakeMethodCall("s", "atoi");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
}

// The integer return type applies to each of the four conversion prototypes,
// not only atoi.
TEST(StringMethods, AtohexReturns32Bit) {
  StringFixture f;
  f.CreateStringVar("s", "1f");
  auto* call = f.MakeMethodCall("s", "atohex");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
}

TEST(StringMethods, AtooctReturns32Bit) {
  StringFixture f;
  f.CreateStringVar("s", "77");
  auto* call = f.MakeMethodCall("s", "atooct");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
}

TEST(StringMethods, AtobinReturns32Bit) {
  StringFixture f;
  f.CreateStringVar("s", "1010");
  auto* call = f.MakeMethodCall("s", "atobin");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
}

// The scan consumes underscore characters along with digits, so they do not
// terminate the conversion and do not contribute to the value.
TEST(StringMethods, AtoiScansUnderscores) {
  StringFixture f;
  f.CreateStringVar("s", "1_000");
  auto* call = f.MakeMethodCall("s", "atoi");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1000u);
}

// Underscore scanning applies to every base, not just decimal.
TEST(StringMethods, AtobinScansUnderscores) {
  StringFixture f;
  f.CreateStringVar("s", "1_010");
  auto* call = f.MakeMethodCall("s", "atobin");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0b1010u);
}

// A leading sign is not part of the integer-literal syntax the conversion
// understands, so it terminates the scan before any digit is seen.
TEST(StringMethods, AtoiDoesNotParseSign) {
  StringFixture f;
  f.CreateStringVar("s", "-5");
  auto* call = f.MakeMethodCall("s", "atoi");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// Size/apostrophe/base notation is not interpreted: the scan stops at the
// apostrophe, keeping only the leading run of digits.
TEST(StringMethods, AtoiDoesNotParseSizedLiteral) {
  StringFixture f;
  f.CreateStringVar("s", "8'd2");
  auto* call = f.MakeMethodCall("s", "atoi");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 8u);
}

// Zero-on-no-digit applies to the octal conversion as well, completing the
// rule across all four methods.
TEST(StringMethods, AtooctNoDigitsReturnsZero) {
  StringFixture f;
  f.CreateStringVar("s", "xyz");
  auto* call = f.MakeMethodCall("s", "atooct");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// Hexadecimal interpretation accepts the uppercase A-F digits, not only the
// lowercase form.
TEST(StringMethods, AtohexUppercaseDigits) {
  StringFixture f;
  f.CreateStringVar("s", "1F");
  auto* call = f.MakeMethodCall("s", "atohex");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0x1Fu);
}

// Octal interpretation rejects a digit outside its base: the scan stops at the
// 8, keeping only the preceding octal run.
TEST(StringMethods, AtooctStopsAtNonOctalDigit) {
  StringFixture f;
  f.CreateStringVar("s", "78");
  auto* call = f.MakeMethodCall("s", "atooct");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 7u);
}

// Binary interpretation rejects a digit outside its base: the scan stops at the
// 2, so "102" yields 0b10.
TEST(StringMethods, AtobinStopsAtNonBinaryDigit) {
  StringFixture f;
  f.CreateStringVar("s", "102");
  auto* call = f.MakeMethodCall("s", "atobin");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0b10u);
}

}  // namespace

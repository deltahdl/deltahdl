#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"
#include "simulator/evaluation.h"

using namespace delta;
namespace {

TEST(UtilitySystemTaskTest, TestPlusargsNotFound) {
  SimFixture f;
  auto* expr =
      MakeSysCall(f.arena, "$test$plusargs", {MkStr(f.arena, "VERBOSE")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(UtilitySystemTaskTest, TestPlusargsPrefixMatch) {
  SimFixture f;
  f.ctx.AddPlusArg("VERBOSE=1");
  auto* expr = MakeSysCall(f.arena, "$test$plusargs", {MkStr(f.arena, "VERB")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

// §21.6: plusargs are scanned in command-line order; a leading plusarg whose
// prefix does not match is skipped so a later matching one still succeeds.
TEST(UtilitySystemTaskTest, TestPlusargsSkipsNonMatchingPlusarg) {
  SimFixture f;
  f.ctx.AddPlusArg("FOO");
  f.ctx.AddPlusArg("BAR=baz");
  auto* expr = MakeSysCall(f.arena, "$test$plusargs", {MkStr(f.arena, "BAR")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

// §21.6: the search string may be an integral variable interpreted as a string,
// and any leading null bytes in that variable are ignored when matching.
TEST(UtilitySystemTaskTest, TestPlusargsFromVariableIgnoresLeadingNulls) {
  SimFixture f;
  f.ctx.AddPlusArg("HELLO");
  auto* pat = f.ctx.CreateVariable("pat", 32);
  // Bytes 'H','E' sit in the low half; the two high bytes are nulls that must
  // not be part of the match string.
  pat->value = MakeLogic4VecVal(f.arena, 32, ('H' << 8) | 'E');
  auto* expr = MakeSysCall(f.arena, "$test$plusargs", {MakeId(f.arena, "pat")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(UtilitySystemTaskTest, ValuePlusargsFound) {
  SimFixture f;
  f.ctx.AddPlusArg("DEPTH=42");
  auto* dest_var = f.ctx.CreateVariable("depth", 32);
  dest_var->value = MakeLogic4VecVal(f.arena, 32, 0);
  auto* expr =
      MakeSysCall(f.arena, "$value$plusargs",
                  {MkStr(f.arena, "DEPTH=%d"), MakeId(f.arena, "depth")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(dest_var->value.ToUint64(), 42u);
}

// §21.6: when more than one plusarg matches the plusarg_string, the first one
// in command-line order supplies the remainder converted into the variable; a
// non-matching earlier plusarg is skipped and a later match is ignored.
TEST(UtilitySystemTaskTest, ValuePlusargsUsesFirstMatchingPlusarg) {
  SimFixture f;
  f.ctx.AddPlusArg("OTHER=1");
  f.ctx.AddPlusArg("VAL=7");
  f.ctx.AddPlusArg("VAL=9");
  auto* val = f.ctx.CreateVariable("val", 32);
  val->value = MakeLogic4VecVal(f.arena, 32, 0);
  auto* expr = MakeSysCall(f.arena, "$value$plusargs",
                           {MkStr(f.arena, "VAL=%d"), MakeId(f.arena, "val")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(val->value.ToUint64(), 7u);
}

TEST(UtilitySystemTaskTest, ValuePlusargsNotFound) {
  SimFixture f;
  auto* dest_var = f.ctx.CreateVariable("depth", 32);
  dest_var->value = MakeLogic4VecVal(f.arena, 32, 7);
  auto* expr =
      MakeSysCall(f.arena, "$value$plusargs",
                  {MkStr(f.arena, "DEPTH=%d"), MakeId(f.arena, "depth")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
  // §21.6: when nothing matches, the destination variable is left unmodified
  // and no warning is generated for the zero return.
  EXPECT_EQ(dest_var->value.ToUint64(), 7u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

// §21.6: %h/%x perform hexadecimal conversion; uppercase and leading-zero forms
// of the format string are equally valid.
TEST(UtilitySystemTaskTest, ValuePlusargsHexUppercaseLeadingZeroForm) {
  SimFixture f;
  f.ctx.AddPlusArg("ADDR=ff");
  auto* dest_var = f.ctx.CreateVariable("addr", 16);
  dest_var->value = MakeLogic4VecVal(f.arena, 16, 0);
  auto* expr =
      MakeSysCall(f.arena, "$value$plusargs",
                  {MkStr(f.arena, "ADDR=%0H"), MakeId(f.arena, "addr")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(dest_var->value.ToUint64(), 255u);
}

// §21.6: %e/%f/%g convert the remainder to a real value stored in the variable.
TEST(UtilitySystemTaskTest, ValuePlusargsRealConversion) {
  SimFixture f;
  f.ctx.AddPlusArg("FREQ+9.234");
  auto* freq = f.ctx.CreateVariable("freq", 64);
  freq->value = MakeLogic4VecVal(f.arena, 64, 0);
  f.ctx.RegisterRealVariable("freq");
  auto* expr =
      MakeSysCall(f.arena, "$value$plusargs",
                  {MkStr(f.arena, "FREQ%0F"), MakeId(f.arena, "freq")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_NEAR(ResultToDouble(freq->value), 9.234, 1e-9);
}

// §21.6: %s stores the remainder characters with no numeric conversion.
TEST(UtilitySystemTaskTest, ValuePlusargsStringConversion) {
  SimFixture f;
  f.ctx.AddPlusArg("NAME=hi");
  auto* name = f.ctx.CreateVariable("name", 32);
  name->value = MakeLogic4VecVal(f.arena, 32, 0);
  auto* expr =
      MakeSysCall(f.arena, "$value$plusargs",
                  {MkStr(f.arena, "NAME=%s"), MakeId(f.arena, "name")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(FormatValueAsString(name->value), "hi");
}

// §21.6: when no remaining string follows the matched prefix, the stored value
// is zero for the numeric conversions.
TEST(UtilitySystemTaskTest, ValuePlusargsEmptyRemainderStoresZero) {
  SimFixture f;
  f.ctx.AddPlusArg("COUNT=");
  auto* count = f.ctx.CreateVariable("count", 32);
  count->value = MakeLogic4VecVal(f.arena, 32, 99);
  auto* expr =
      MakeSysCall(f.arena, "$value$plusargs",
                  {MkStr(f.arena, "COUNT=%d"), MakeId(f.arena, "count")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(count->value.ToUint64(), 0u);
}

// §21.6: a remainder containing characters illegal for the conversion writes
// the variable with 'bx. Here '2' is not a legal binary digit.
TEST(UtilitySystemTaskTest, ValuePlusargsIllegalCharsStoreX) {
  SimFixture f;
  f.ctx.AddPlusArg("FLAG=12");
  auto* flag = f.ctx.CreateVariable("flag", 8);
  flag->value = MakeLogic4VecVal(f.arena, 8, 0);
  auto* expr =
      MakeSysCall(f.arena, "$value$plusargs",
                  {MkStr(f.arena, "FLAG=%b"), MakeId(f.arena, "flag")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_FALSE(flag->value.IsKnown());
}

// §21.6: a negative value is treated as larger than the variable, so it is
// truncated to the variable width.
TEST(UtilitySystemTaskTest, ValuePlusargsNegativeValueTruncates) {
  SimFixture f;
  f.ctx.AddPlusArg("OFF=-1");
  auto* off = f.ctx.CreateVariable("off", 8);
  off->value = MakeLogic4VecVal(f.arena, 8, 0);
  auto* expr = MakeSysCall(f.arena, "$value$plusargs",
                           {MkStr(f.arena, "OFF=%d"), MakeId(f.arena, "off")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(off->value.ToUint64(), 255u);
}

}  // namespace

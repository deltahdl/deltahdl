#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "simulator/dpi_runtime.h"

using namespace delta;

namespace {

// §35.6.1 — Argument passing. Argument compatibility and coercion rules are the
// same as for native SystemVerilog functions: when a coercion is needed the
// value crosses the interface through a temporary that is created with the
// appropriate coercion. For input and inout arguments the temporary is
// initialized with the actual coerced to the formal's type (copy-in); for
// output and inout arguments the temporary's value is assigned back to the
// actual with the appropriate conversion (copy-out). These tests observe
// DpiRuntime::CallImportWithArgs applying that coercion across the boundary.

// P2b copy-in: a wider actual (longint) bound to a narrower formal (int) is
// coerced to the formal's type before the foreign function sees it.
TEST(DpiArgumentPassing, InputActualCoercedToFormalTypeOnCopyIn) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_take_int";
  func.sv_name = "take_int";
  func.return_type = DataTypeKind::kInt;
  func.args = {DpiArg{"x", DataTypeKind::kInt, Direction::kInput}};
  // The foreign function reports the type tag and value it actually observed.
  func.arg_impl = [](std::vector<DpiArgValue>& a) {
    bool is_int = a[0].type == DataTypeKind::kInt;
    return DpiArgValue::FromInt(is_int ? a[0].AsInt() : -1);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromLongint(42)};
  DpiArgValue result = rt.CallImportWithArgs("take_int", actuals);

  // The callee saw an int formal carrying the coerced value, not the original
  // longint actual.
  EXPECT_EQ(result.AsInt(), 42);
}

// P2b + P3b: coercion across the interface follows general SystemVerilog
// assignment rules. A real actual bound to an integer formal rounds to the
// nearest integer, just as a real-to-integer assignment would.
TEST(DpiArgumentPassing, RealInputCoercedToIntegerFormalRoundsLikeAssignment) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_take_int";
  func.sv_name = "take_int";
  func.return_type = DataTypeKind::kInt;
  func.args = {DpiArg{"x", DataTypeKind::kInt, Direction::kInput}};
  func.arg_impl = [](std::vector<DpiArgValue>& a) {
    return DpiArgValue::FromInt(a[0].type == DataTypeKind::kInt ? a[0].AsInt()
                                                                : -1);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromReal(3.7)};
  DpiArgValue result = rt.CallImportWithArgs("take_int", actuals);

  EXPECT_EQ(result.AsInt(), 4);  // 3.7 rounds to 4 as for an assignment
}

// P2b copy-out: an output formal narrower than the actual has its
// foreign-written value coerced back to the actual's wider type on copy-out.
TEST(DpiArgumentPassing, OutputValueCoercedToActualTypeOnCopyOut) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_produce_int";
  func.sv_name = "produce_int";
  func.return_type = DataTypeKind::kVoid;
  func.args = {DpiArg{"y", DataTypeKind::kInt, Direction::kOutput}};
  func.arg_impl = [](std::vector<DpiArgValue>& a) {
    a[0] = DpiArgValue::FromInt(7);
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(std::move(func));

  // The actual is a longint; the formal is an int.
  std::vector<DpiArgValue> actuals = {DpiArgValue::FromLongint(0)};
  rt.CallImportWithArgs("produce_int", actuals);

  // The int the foreign code wrote is coerced back to the actual's longint
  // type.
  EXPECT_EQ(actuals[0].type, DataTypeKind::kLongint);
  EXPECT_EQ(actuals[0].AsLongint(), 7);
}

// P2b inout: both directions are coerced — the actual is coerced to the formal
// type on copy-in and the written-back value is coerced to the actual type on
// copy-out.
TEST(DpiArgumentPassing, InoutCoercedBothDirections) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_bump";
  func.sv_name = "bump";
  func.return_type = DataTypeKind::kVoid;
  func.args = {DpiArg{"z", DataTypeKind::kInt, Direction::kInout}};
  // The foreign function observes its int formal and writes back one more.
  func.arg_impl = [](std::vector<DpiArgValue>& a) {
    int32_t seen = a[0].type == DataTypeKind::kInt ? a[0].AsInt() : -1;
    a[0] = DpiArgValue::FromInt(seen + 1);
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromLongint(10)};
  rt.CallImportWithArgs("bump", actuals);

  // Copy-in delivered the longint coerced to int (10); copy-out coerced the
  // written-back int (11) to the actual's longint type.
  EXPECT_EQ(actuals[0].type, DataTypeKind::kLongint);
  EXPECT_EQ(actuals[0].AsLongint(), 11);
}

// P3a/P3c/P4a observed at the §35.6.1 framing: input arguments are passed as if
// by copy-in, so a foreign modification to the input copy is not visible
// outside and the actual is not changed by the callee.
TEST(DpiArgumentPassing, InputCopyInLeavesActualUnaffected) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_clobber";
  func.sv_name = "clobber";
  func.return_type = DataTypeKind::kInt;
  func.args = {DpiArg{"x", DataTypeKind::kInt, Direction::kInput}};
  func.arg_impl = [](std::vector<DpiArgValue>& a) {
    int32_t seen = a[0].AsInt();
    a[0] = DpiArgValue::FromInt(-999);  // modify the copy-in temporary
    return DpiArgValue::FromInt(seen);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(5)};
  DpiArgValue result = rt.CallImportWithArgs("clobber", actuals);

  EXPECT_EQ(result.AsInt(), 5);      // the callee did receive the actual
  EXPECT_EQ(actuals[0].AsInt(), 5);  // but the actual is unaffected
}

// P2b edge: coercion happens only when needed. When the actual already matches
// the formal's type no temporary/conversion is introduced, and the value the
// callee sees is the actual untouched.
TEST(DpiArgumentPassing, MatchingTypeArgumentPassesWithoutCoercion) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_echo";
  func.sv_name = "echo";
  func.return_type = DataTypeKind::kLongint;
  func.args = {DpiArg{"x", DataTypeKind::kLongint, Direction::kInput}};
  // Report both the type tag and the value the callee observed.
  func.arg_impl = [](std::vector<DpiArgValue>& a) {
    bool is_longint = a[0].type == DataTypeKind::kLongint;
    return DpiArgValue::FromLongint(is_longint ? a[0].AsLongint() : -1);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromLongint(123456789012)};
  DpiArgValue result = rt.CallImportWithArgs("echo", actuals);

  // No coercion was applied: the longint actual reached the longint formal
  // unchanged, full 64-bit value intact.
  EXPECT_EQ(result.AsLongint(), 123456789012);
}

// P2b/P3b edge: a copy-in coercion that narrows follows assignment rules — a
// 64-bit actual whose value does not fit the 32-bit formal is truncated, as a
// longint-to-int assignment would be.
TEST(DpiArgumentPassing, NarrowingInputCoercionTruncatesLikeAssignment) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_take_int";
  func.sv_name = "take_int";
  func.return_type = DataTypeKind::kInt;
  func.args = {DpiArg{"x", DataTypeKind::kInt, Direction::kInput}};
  func.arg_impl = [](std::vector<DpiArgValue>& a) {
    return DpiArgValue::FromInt(a[0].type == DataTypeKind::kInt ? a[0].AsInt()
                                                                : -1);
  };
  rt.RegisterImport(std::move(func));

  // 0x1_0000_0007 — the low 32 bits are 7; the high bit beyond int width is
  // dropped by the narrowing coercion.
  std::vector<DpiArgValue> actuals = {DpiArgValue::FromLongint(0x100000007LL)};
  DpiArgValue result = rt.CallImportWithArgs("take_int", actuals);

  EXPECT_EQ(result.AsInt(), 7);  // truncated to the formal's 32-bit width
}

// P2b/P3b edge: the conversion on copy-out also follows assignment rules in the
// reverse direction — a real value written to a real output formal is rounded
// when assigned back to an integer actual.
TEST(DpiArgumentPassing, OutputRealRoundedToIntegerActualOnCopyOut) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_produce_real";
  func.sv_name = "produce_real";
  func.return_type = DataTypeKind::kVoid;
  func.args = {DpiArg{"y", DataTypeKind::kReal, Direction::kOutput}};
  func.arg_impl = [](std::vector<DpiArgValue>& a) {
    a[0] = DpiArgValue::FromReal(2.9);
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(std::move(func));

  // The actual is an int; the formal is a real.
  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(0)};
  rt.CallImportWithArgs("produce_real", actuals);

  // 2.9 is rounded to 3 as it is converted to the int actual on copy-out.
  EXPECT_EQ(actuals[0].type, DataTypeKind::kInt);
  EXPECT_EQ(actuals[0].AsInt(), 3);
}

}  // namespace

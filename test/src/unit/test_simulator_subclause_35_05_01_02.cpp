#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "simulator/dpi_runtime.h"

using namespace delta;

namespace {

// §35.5.1.2: a formal input argument shall not be modified. If the imported
// function changes its copy, the change shall not be visible outside the
// function and the actual argument shall not be changed.
TEST(DpiArgumentDirections, InputActualUnchangedAfterForeignModification) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_consume";
  func.sv_name = "consume";
  func.return_type = DataTypeKind::kInt;
  func.args = {DpiArg{"x", DataTypeKind::kInt, Direction::kInput}};
  // The foreign function reports the value it saw on entry, then clobbers its
  // copy of the input argument.
  func.arg_impl = [](std::vector<DpiArgValue>& a) {
    int32_t seen = a[0].AsInt();
    a[0] = DpiArgValue::FromInt(-1);
    return DpiArgValue::FromInt(seen);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(7)};
  DpiArgValue result = rt.CallImportWithArgs("consume", actuals);

  // The callee did receive the actual value...
  EXPECT_EQ(result.AsInt(), 7);
  // ...but the actual is not changed by the foreign modification.
  EXPECT_EQ(actuals[0].AsInt(), 7);
}

// §35.5.1.2: the imported function shall not assume anything about the initial
// value of a formal output argument; that value is undetermined. The callee
// therefore does not observe the caller's actual on an output formal, and the
// value the foreign function writes is visible outside the call.
TEST(DpiArgumentDirections, OutputInitialUndeterminedAndWritebackVisible) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_produce";
  func.sv_name = "produce";
  func.return_type = DataTypeKind::kVoid;
  func.args = {DpiArg{"y", DataTypeKind::kInt, Direction::kOutput}};
  int32_t observed_initial = 12345;
  func.arg_impl = [&observed_initial](std::vector<DpiArgValue>& a) {
    observed_initial = a[0].AsInt();
    a[0] = DpiArgValue::FromInt(42);
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(999)};
  rt.CallImportWithArgs("produce", actuals);

  // The caller's actual is not handed to the callee as the output's initial
  // value; an undetermined (here zeroed) value is supplied instead.
  EXPECT_NE(observed_initial, 999);
  EXPECT_EQ(observed_initial, 0);
  // The value the foreign function wrote is visible outside the call.
  EXPECT_EQ(actuals[0].AsInt(), 42);
}

// §35.5.1.2: the imported function can access the initial value of a formal
// inout argument, and changes it makes to that argument shall be visible
// outside the function.
TEST(DpiArgumentDirections, InoutInitialReadableAndWritebackVisible) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_bump";
  func.sv_name = "bump";
  func.return_type = DataTypeKind::kVoid;
  func.args = {DpiArg{"z", DataTypeKind::kInt, Direction::kInout}};
  int32_t observed_initial = -1;
  func.arg_impl = [&observed_initial](std::vector<DpiArgValue>& a) {
    observed_initial = a[0].AsInt();
    a[0] = DpiArgValue::FromInt(a[0].AsInt() + 1);
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(7)};
  rt.CallImportWithArgs("bump", actuals);

  // The foreign function can read the inout argument's initial value...
  EXPECT_EQ(observed_initial, 7);
  // ...and its change is visible outside the call.
  EXPECT_EQ(actuals[0].AsInt(), 8);
}

// §35.5.1.2: a single imported function can mix input, output, and inout
// formals. Each direction follows its own rule within one call: the input
// actual is unchanged, the output is seeded with an undetermined value and its
// write is visible, and the inout's initial value is readable and its write is
// visible.
TEST(DpiArgumentDirections, MixedDirectionArgumentsHandledInOneCall) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_mix";
  func.sv_name = "mix";
  func.return_type = DataTypeKind::kVoid;
  func.args = {
      DpiArg{"a", DataTypeKind::kInt, Direction::kInput},
      DpiArg{"b", DataTypeKind::kInt, Direction::kOutput},
      DpiArg{"c", DataTypeKind::kInt, Direction::kInout},
  };
  int32_t seen_in = -1;
  int32_t seen_out = -1;
  int32_t seen_io = -1;
  func.arg_impl = [&](std::vector<DpiArgValue>& a) {
    seen_in = a[0].AsInt();
    seen_out = a[1].AsInt();
    seen_io = a[2].AsInt();
    // The foreign function writes all three formals.
    a[0] = DpiArgValue::FromInt(111);          // input write — discarded
    a[1] = DpiArgValue::FromInt(222);          // output write — visible
    a[2] = DpiArgValue::FromInt(seen_io + 1);  // inout write — visible
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(5),
                                      DpiArgValue::FromInt(900),
                                      DpiArgValue::FromInt(7)};
  rt.CallImportWithArgs("mix", actuals);

  // Input: the callee saw the actual, but the actual is left unchanged.
  EXPECT_EQ(seen_in, 5);
  EXPECT_EQ(actuals[0].AsInt(), 5);
  // Output: the callee did not see the actual 900; the write is visible.
  EXPECT_NE(seen_out, 900);
  EXPECT_EQ(seen_out, 0);
  EXPECT_EQ(actuals[1].AsInt(), 222);
  // Inout: the callee saw the initial 7; the write is visible.
  EXPECT_EQ(seen_io, 7);
  EXPECT_EQ(actuals[2].AsInt(), 8);
}

// §35.5.1.2: the undetermined initial value supplied for an output argument
// matches the formal's type rather than being forced to an int. A real output
// formal is seeded with a real zero, not the caller's actual, and the written
// real value is visible outside the call.
TEST(DpiArgumentDirections, OutputUndeterminedSeedMatchesNonIntFormalType) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_rout";
  func.sv_name = "rout";
  func.return_type = DataTypeKind::kVoid;
  func.args = {DpiArg{"r", DataTypeKind::kReal, Direction::kOutput}};
  double seen = 1.0;
  func.arg_impl = [&seen](std::vector<DpiArgValue>& a) {
    seen = a[0].AsReal();
    a[0] = DpiArgValue::FromReal(2.5);
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromReal(99.0)};
  rt.CallImportWithArgs("rout", actuals);

  // The real output formal is not handed the caller's actual; it receives an
  // undetermined (zeroed) real value instead.
  EXPECT_NE(seen, 99.0);
  EXPECT_DOUBLE_EQ(seen, 0.0);
  // The written real value is visible outside the call.
  EXPECT_DOUBLE_EQ(actuals[0].AsReal(), 2.5);
}

// §35.5.1.2: the undetermined initial value supplied for an output argument is
// type-correct for a string formal too. A string output is seeded with an
// undetermined value (an empty string) rather than the caller's actual string,
// and the string the foreign function writes is visible outside the call. This
// exercises the string branch of the undetermined-seed selection, which stores
// its value differently from the scalar branches.
TEST(DpiArgumentDirections, OutputUndeterminedSeedForStringFormalIsNotActual) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_sout";
  func.sv_name = "sout";
  func.return_type = DataTypeKind::kVoid;
  func.args = {DpiArg{"s", DataTypeKind::kString, Direction::kOutput}};
  std::string seen = "sentinel";
  func.arg_impl = [&seen](std::vector<DpiArgValue>& a) {
    seen = a[0].AsString();
    a[0] = DpiArgValue::FromString("written");
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromString("caller")};
  rt.CallImportWithArgs("sout", actuals);

  // The string output formal does not receive the caller's actual string; it
  // gets an undetermined (empty) string instead.
  EXPECT_NE(seen, "caller");
  EXPECT_EQ(seen, "");
  // The written string is visible outside the call.
  EXPECT_EQ(actuals[0].AsString(), "written");
}

// §35.5.1.2: the undetermined output seed is type-correct for a longint formal
// as well — the callee sees a zeroed 64-bit value, not the caller's actual, and
// the written longint is visible outside the call. This exercises the longint
// branch of the undetermined-seed selection.
TEST(DpiArgumentDirections, OutputUndeterminedSeedForLongintFormalIsNotActual) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_lout";
  func.sv_name = "lout";
  func.return_type = DataTypeKind::kVoid;
  func.args = {DpiArg{"l", DataTypeKind::kLongint, Direction::kOutput}};
  int64_t seen = 0x7fffffffffffffffLL;
  func.arg_impl = [&seen](std::vector<DpiArgValue>& a) {
    seen = a[0].AsLongint();
    a[0] = DpiArgValue::FromLongint(0x0123456789abcdefLL);
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {
      DpiArgValue::FromLongint(0x1111222233334444LL)};
  rt.CallImportWithArgs("lout", actuals);

  // The longint output formal is seeded with an undetermined (zeroed) value
  // rather than the caller's actual.
  EXPECT_NE(seen, 0x1111222233334444LL);
  EXPECT_EQ(seen, 0);
  // The written 64-bit value is visible outside the call.
  EXPECT_EQ(actuals[0].AsLongint(), 0x0123456789abcdefLL);
}

// §35.5.1.2: an import registered with the input-only callback (no direction-
// aware implementation) is still callable through the direction-aware path.
// Because that callback cannot write its arguments, an input actual is left
// unchanged — the input-argument rule holds on this path too.
TEST(DpiArgumentDirections, LegacyInputOnlyCallbackLeavesActualUnchanged) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_legacy";
  func.sv_name = "legacy";
  func.return_type = DataTypeKind::kInt;
  func.args = {DpiArg{"x", DataTypeKind::kInt, Direction::kInput}};
  func.impl = [](const std::vector<DpiArgValue>& a) {
    return DpiArgValue::FromInt(a[0].AsInt() * 2);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(6)};
  DpiArgValue result = rt.CallImportWithArgs("legacy", actuals);

  // The input-only callback ran on the actual...
  EXPECT_EQ(result.AsInt(), 12);
  // ...and the input actual is unchanged.
  EXPECT_EQ(actuals[0].AsInt(), 6);
}

}  // namespace

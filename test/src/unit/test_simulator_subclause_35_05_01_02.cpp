#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "common/types.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/dpi.h"
#include "simulator/dpi_runtime.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

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

// ---------------------------------------------------------------------------
// The same three rules, asked of a call a design makes.
//
// The cases above call the foreign function through DpiRuntime, which is the
// registry the DPI C layer in src/simulator/svdpi.cpp works against. A call
// written in SystemVerilog does not reach it: EvalDpiCall in
// src/simulator/eval_function.cpp evaluates the call site's actuals, calls the
// import through the DpiContext the run holds, and is where a value the foreign
// function wrote has to arrive if it is to be visible to the design at all.
// §35.5.1.2 is a rule about what the calling code sees, so it is asked here of
// the code that does the seeing.
// ---------------------------------------------------------------------------

// The import the cases below call: a foreign function of one formal, which
// reports the value it was handed and leaves `wrote` in its place. The formal's
// direction is all that varies between the cases, so each says which direction
// it is about and nothing else.
DpiFunction OneFormalImport(Direction direction, uint64_t wrote,
                            uint64_t* seen) {
  DpiFunction func;
  func.c_name = "c_touch";
  func.sv_name = "touch";
  func.return_type = DataTypeKind::kInt;
  func.args = {DpiArg{"a", DataTypeKind::kInt, direction}};
  func.arg_impl = [wrote, seen](std::vector<uint64_t>& args) -> uint64_t {
    *seen = args[0];
    args[0] = wrote;
    return 0;
  };
  return func;
}

// A design holding one variable `a`, which is handed to that import and read
// back afterwards. Both halves of every rule below are answered off this: what
// the foreign function was handed is `seen`, and what the call site is left
// holding is Actual().
struct TouchingAnActual {
  DpiContext dpi;
  SimFixture f;
  uint64_t seen = 0;

  TouchingAnActual(Direction direction, uint64_t wrote, uint64_t actual) {
    dpi.RegisterImport(OneFormalImport(direction, wrote, &seen));
    f.ctx.SetDpiContext(&dpi);
    auto* var = f.ctx.CreateVariable("a", 32);
    var->value = MakeLogic4VecVal(f.arena, 32, actual);
    EvalFunctionCall(ParseExprFrom("touch(a)", f), f.ctx, f.arena);
  }

  uint64_t Actual() { return f.ctx.FindVariable("a")->value.ToUint64(); }
};

// §35.5.1.2: the actual argument written against an input formal shall not be
// changed. The foreign function writes the formal, and the variable the call
// site named still holds what it held before the call.
TEST(DpiArgumentDirectionsInADesign, AnInputActualIsNotChangedByTheCall) {
  TouchingAnActual run(Direction::kInput, 111, 5);
  EXPECT_EQ(run.Actual(), 5U);
}

// The other half of that rule: the foreign function was handed the actual's
// value in the first place. Without this the case above would hold of a call
// that passed nothing at all.
TEST(DpiArgumentDirectionsInADesign, AnInputActualReachesTheImport) {
  TouchingAnActual run(Direction::kInput, 111, 5);
  EXPECT_EQ(run.seen, 5U);
}

// §35.5.1.2: the changes an imported function makes to an output formal are
// visible outside the function, so the variable the call site named holds what
// the foreign function wrote once the call has returned.
TEST(DpiArgumentDirectionsInADesign, AnOutputActualTakesWhatTheImportWrote) {
  TouchingAnActual run(Direction::kOutput, 42, 900);
  EXPECT_EQ(run.Actual(), 42U);
}

// §35.5.1.2: an imported function shall not assume anything about the initial
// value of an output formal, that value being undetermined. So the call does
// not hand the actual in, and a foreign function reading the formal on entry
// does not read what the design last assigned to that variable.
TEST(DpiArgumentDirectionsInADesign, AnOutputFormalIsNotHandedTheActual) {
  TouchingAnActual run(Direction::kOutput, 42, 900);
  EXPECT_NE(run.seen, 900U);
}

// §35.5.1.2: an imported function can access the initial value of an inout
// formal. That is what separates the direction from output, which the case
// above has arriving with the actual withheld.
TEST(DpiArgumentDirectionsInADesign, AnInoutFormalIsHandedTheActual) {
  TouchingAnActual run(Direction::kInout, 8, 7);
  EXPECT_EQ(run.seen, 7U);
}

// §35.5.1.2: and the changes it makes to an inout formal are visible outside
// the function, which is what separates the direction from input.
TEST(DpiArgumentDirectionsInADesign, AnInoutActualTakesWhatTheImportWrote) {
  TouchingAnActual run(Direction::kInout, 8, 7);
  EXPECT_EQ(run.Actual(), 8U);
}

// The formal a written value belongs to is the one the call site bound it to,
// which §35.6 lets a call name rather than count. A call binding its actuals by
// name therefore leaves each value with the variable that formal was named
// against, and not with the one standing in that position.
TEST(DpiArgumentDirectionsInADesign, ANamedActualTakesItsOwnFormalsValue) {
  DpiContext dpi;
  SimFixture f;
  DpiFunction func;
  func.c_name = "c_pair";
  func.sv_name = "pair";
  func.return_type = DataTypeKind::kInt;
  func.args = {DpiArg{"first", DataTypeKind::kInt, Direction::kOutput},
               DpiArg{"second", DataTypeKind::kInt, Direction::kOutput}};
  func.arg_impl = [](std::vector<uint64_t>& args) -> uint64_t {
    args[0] = 11;
    args[1] = 22;
    return 0;
  };
  dpi.RegisterImport(func);
  f.ctx.SetDpiContext(&dpi);
  f.ctx.CreateVariable("one", 32)->value = MakeLogic4VecVal(f.arena, 32, 0);
  f.ctx.CreateVariable("two", 32)->value = MakeLogic4VecVal(f.arena, 32, 0);

  EvalFunctionCall(ParseExprFrom("pair(.second(two), .first(one))", f), f.ctx,
                   f.arena);

  EXPECT_EQ(f.ctx.FindVariable("two")->value.ToUint64(), 22U);
}

// An import declaring input formals alone is written with the reading form of
// the implementation, which cannot change an argument at all. A design calling
// one is answered by it as before: nothing the call copies back is a value the
// foreign function did not write, so the result is what it computed.
TEST(DpiArgumentDirectionsInADesign, AnImportWritingNothingYieldsItsResult) {
  DpiContext dpi;
  SimFixture f;
  DpiFunction func;
  func.c_name = "c_double";
  func.sv_name = "twice";
  func.return_type = DataTypeKind::kInt;
  func.args = {DpiArg{"a", DataTypeKind::kInt, Direction::kInput}};
  func.impl = [](const std::vector<uint64_t>& args) -> uint64_t {
    return args[0] * 2;
  };
  dpi.RegisterImport(func);
  f.ctx.SetDpiContext(&dpi);
  f.ctx.CreateVariable("a", 32)->value = MakeLogic4VecVal(f.arena, 32, 6);

  auto result =
      EvalFunctionCall(ParseExprFrom("twice(a)", f), f.ctx, f.arena).ToUint64();

  EXPECT_EQ(result, 12U);
}

}  // namespace

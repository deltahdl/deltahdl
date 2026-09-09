#include <gtest/gtest.h>

#include <cstdint>
#include <utility>
#include <vector>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_dpi_take_int.h"
#include "parser/ast.h"
#include "simulator/dpi_runtime.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

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
  DpiArgValue result =
      CallTakeIntReportingFormal(rt, DpiArgValue::FromReal(3.7));

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
  // 0x1_0000_0007 — the low 32 bits are 7; the high bit beyond int width is
  // dropped by the narrowing coercion.
  DpiArgValue result =
      CallTakeIntReportingFormal(rt, DpiArgValue::FromLongint(0x100000007LL));

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

// ---------------------------------------------------------------------------
// The same copy-in and copy-out, asked of a call a design writes with an
// argument whose bits are not all known.
//
// The cases above call the foreign function through DpiRuntime directly.
// EvalDpiCall in src/simulator/eval_function_dpi.cpp evaluates the call site's
// actuals and calls the import through the DpiRuntime the run holds. §35.2.2.1
// rules that "The implementation (representation and layout) of 4-state values,
// structures, and arrays is irrelevant for SystemVerilog semantics and can only
// impact the foreign side of the interface", so an x or a z the design wrote
// has to survive that crossing in both directions.
// ---------------------------------------------------------------------------

// A design holding one four-bit variable `a` set to `actual`, handed to an
// import declared in `direction`. `seen` is the aval/bval pair the foreign
// body was handed, `wrote` is what that body leaves in the formal, and
// Actual() is what the variable holds once the call has returned.
//
// The formal is declared integer, which §35.5.6 lists among the permitted
// types of a formal argument and which is four-state, so a value with an
// unknown bit is one the formal can hold.
struct FourStateActual {
  DpiRuntime dpi;
  SimFixture f;
  SvLogicVecVal seen = {};

  FourStateActual(Direction direction, SvLogicVecVal actual,
                  SvLogicVecVal wrote) {
    DpiRtFunction func;
    func.c_name = "c_touch_4state";
    func.sv_name = "touch4";
    func.return_type = DataTypeKind::kInt;
    func.args = {DpiArg{"a", DataTypeKind::kInteger, direction}};
    SvLogicVecVal* seen_slot = &seen;
    func.arg_impl = [seen_slot,
                     wrote](std::vector<DpiArgValue>& args) -> DpiArgValue {
      *seen_slot = args[0].AsLogicVec();
      args[0] = DpiArgValue::FromLogicVec(wrote);
      return DpiArgValue::FromInt(0);
    };
    dpi.RegisterImport(std::move(func));
    f.ctx.SetDpiRuntime(&dpi);
    auto* var = f.ctx.CreateVariable("a", 4);
    var->value = MakeLogic4Vec(f.arena, 4);
    var->value.words[0] = Logic4Word{actual.aval, actual.bval};
    EvalFunctionCall(ParseExprFrom("touch4(a)", f), f.ctx, f.arena);
  }

  Logic4Word Actual() { return f.ctx.FindVariable("a")->value.words[0]; }
};

// §35.5.6's packed formal as a declaration writes it: the bit or logic type it
// is composed of, the width, and the direction §35.5.1.2 reads to decide which
// way the value crosses. Those three are what decide the carrier, so they
// travel together rather than as loose arguments.
struct PackedFormal {
  DataTypeKind kind = DataTypeKind::kBit;
  uint32_t width = 128;
  Direction direction = Direction::kInput;
};

// The same crossing for a formal §35.5.6 admits at a width the union member its
// kind lands in cannot hold. `k` is a variable of the formal's width whose two
// words are `lo` and `hi`, so the value travels in Annex H.10.1.2's canonical
// array of aval/bval pairs rather than in the union. `seen` is the array the
// foreign body was handed, `wrote` is the array it leaves in the formal, and
// Actual() is the variable once the call has returned.
struct WideActual {
  DpiRuntime dpi;
  SimFixture f;
  std::vector<SvLogicVecVal> seen;

  WideActual(PackedFormal decl, Logic4Word lo, Logic4Word hi,
             const std::vector<SvLogicVecVal>& wrote) {
    DpiRtFunction func;
    func.c_name = "c_touch_wide";
    func.sv_name = "touch_wide";
    func.return_type = DataTypeKind::kInt;
    DpiArg formal;
    formal.name = "k";
    formal.type = decl.kind;
    formal.direction = decl.direction;
    formal.width = decl.width;
    func.args = {formal};
    auto* seen_slot = &seen;
    func.arg_impl = [seen_slot, wrote,
                     decl](std::vector<DpiArgValue>& args) -> DpiArgValue {
      *seen_slot = args[0].AsLogicVecWords();
      if (!wrote.empty()) {
        args[0] = DpiArgValue::FromLogicVecWords(wrote, decl.width, decl.kind);
      }
      return DpiArgValue::FromInt(0);
    };
    dpi.RegisterImport(std::move(func));
    f.ctx.SetDpiRuntime(&dpi);
    auto* var = f.ctx.CreateVariable("k", decl.width);
    var->value = MakeLogic4Vec(f.arena, decl.width);
    var->value.words[0] = lo;
    if (var->value.nwords > 1) var->value.words[1] = hi;
    EvalFunctionCall(ParseExprFrom("touch_wide(k)", f), f.ctx, f.arena);
  }

  const Logic4Vec& Actual() { return f.ctx.FindVariable("k")->value; }
};

// §35.5.6 lists "Packed arrays, structs, and unions composed of types bit and
// logic" among a formal's permitted types and puts no width limit on one, so
// `bit [127:0]` is a formal a declaration may write. The actual's four 32-bit
// quarters differ from one another, so a crossing that keeps the first word
// alone hands the foreign body the low two and nothing above them.
TEST(DpiArgumentPassingInADesign, AFormalWiderThanOneWordArrivesWhole) {
  WideActual run(PackedFormal{}, Logic4Word{0x1234567855667788ULL, 0},
                 Logic4Word{0x99AABBCCDDEEFF00ULL, 0}, {});

  ASSERT_EQ(run.seen.size(), 4u);
  EXPECT_EQ(run.seen[0].aval, 0x55667788U);
  EXPECT_EQ(run.seen[1].aval, 0x12345678U);
  // These two are the halves a single-word carrier drops entirely.
  EXPECT_EQ(run.seen[2].aval, 0xDDEEFF00U);
  EXPECT_EQ(run.seen[3].aval, 0x99AABBCCU);
}

// §35.2.2.1 has the representation of a four-state value be "irrelevant for
// SystemVerilog semantics", so an unknown bit crosses wherever it stands in the
// value. Bit 96 is x here -- aval and bval both set in the top quarter -- and
// bit 0 is 1, so a carrier that widened the aval and left the bval one word
// wide delivers bit 96 as a known one.
TEST(DpiArgumentPassingInADesign, AnUnknownBitAboveTheFirstWordSurvives) {
  WideActual run(PackedFormal{}, Logic4Word{1, 0},
                 Logic4Word{0x0000000100000000ULL, 0x0000000100000000ULL}, {});

  ASSERT_EQ(run.seen.size(), 4u);
  EXPECT_EQ(run.seen[0].aval, 1U);
  EXPECT_EQ(run.seen[0].bval, 0U);
  EXPECT_EQ(run.seen[3].aval, 1U);
  EXPECT_EQ(run.seen[3].bval, 1U);
}

// §35.6.1: "For output or inout arguments, the value of the temporary variable
// is assigned to the actual argument with the appropriate conversion." The
// foreign body leaves all four quarters set to different values, so the
// variable the call site named holds every one of them afterwards.
TEST(DpiArgumentPassingInADesign, AWideOutputFormalIsWrittenBackWhole) {
  WideActual run(
      PackedFormal{DataTypeKind::kBit, 128, Direction::kOutput}, Logic4Word{},
      Logic4Word{},
      {SvLogicVecVal{0x0A0B0C0DU, 0}, SvLogicVecVal{0x1A1B1C1DU, 0},
       SvLogicVecVal{0x2A2B2C2DU, 0}, SvLogicVecVal{0x3A3B3C3DU, 0}});

  const Logic4Vec& got = run.Actual();
  ASSERT_EQ(got.width, 128U);
  ASSERT_GE(got.nwords, 2U);
  EXPECT_EQ(got.words[0].aval, 0x1A1B1C1D0A0B0C0DULL);
  // The upper word is what a write-back built from words[0] alone leaves at 0.
  EXPECT_EQ(got.words[1].aval, 0x3A3B3C3D2A2B2C2DULL);
}

// §35.5.6 puts no lower bound on a packed formal either, and what decides
// whether the union can hold one is the member its kind lands in rather than
// the widest member there is: SvBit is a uint8_t holding one bit, so a
// `bit [7:0]` formal has seven bits with nowhere to go. The actual is 8'hA5,
// whose bit 0 is 1, so a crossing that keeps that member hands the foreign body
// a 1 and reads as the whole value having arrived.
TEST(DpiArgumentPassingInADesign,
     APackedFormalNarrowerThanOneWordArrivesWhole) {
  WideActual run(PackedFormal{DataTypeKind::kBit, 8, Direction::kInput},
                 Logic4Word{0xA5, 0}, Logic4Word{}, {});

  ASSERT_EQ(run.seen.size(), 1u);
  EXPECT_EQ(run.seen[0].aval, 0xA5U);
}

// The four-state half of the same: §35.5.6's packed types are "composed of
// types bit and logic", and a logic holds four values, so an unknown bit of a
// `logic [7:0]` formal crosses wherever it stands. Bit 4 is x here -- aval and
// bval both set -- and the SvLogic member the kind would otherwise land in
// carries one bit of each half.
TEST(DpiArgumentPassingInADesign, AnUnknownBitOfAPackedLogicFormalSurvives) {
  WideActual run(PackedFormal{DataTypeKind::kLogic, 8, Direction::kInput},
                 Logic4Word{0x13, 0x10}, Logic4Word{}, {});

  ASSERT_EQ(run.seen.size(), 1u);
  EXPECT_EQ(run.seen[0].aval, 0x13U);
  EXPECT_EQ(run.seen[0].bval, 0x10U);
}

// §35.6.1's copy-out for the same formal: the foreign body leaves 8'h3C in an
// `output bit [7:0]`, so the variable the call site named holds all eight bits
// afterwards rather than bit 0 of them.
TEST(DpiArgumentPassingInADesign,
     APackedOutputFormalNarrowerThanOneWordIsWrittenBackWhole) {
  WideActual run(PackedFormal{DataTypeKind::kBit, 8, Direction::kOutput},
                 Logic4Word{}, Logic4Word{}, {SvLogicVecVal{0x3C, 0}});

  const Logic4Vec& got = run.Actual();
  ASSERT_EQ(got.width, 8U);
  ASSERT_GE(got.nwords, 1U);
  EXPECT_EQ(got.words[0].aval, 0x3CU);
}

// §35.6.1: "For input and inout arguments, the temporary variable is
// initialized with the value of the actual argument with the appropriate
// coercion." The actual is 4'b10x1, so the foreign body is handed a 1, a 0 and
// an x; an x is aval 1 with bval 1, which one word per bit cannot record.
TEST(DpiArgumentPassingInADesign, AnInputActualsUnknownBitReachesTheImport) {
  FourStateActual run(Direction::kInput, SvLogicVecVal{0b1011, 0b0010},
                      SvLogicVecVal{});

  // Both halves are asserted because either alone is met by a carrier that
  // drops one of them: Logic4Vec::ToUint64 reads 4'b10x1 as 4'b1001, which is
  // neither this aval nor this bval.
  EXPECT_EQ(run.seen.aval, 0b1011U);
  EXPECT_EQ(run.seen.bval, 0b0010U);
}

// §35.2.2.1 has the representation of a 4-state value be "irrelevant for
// SystemVerilog semantics", so §35.6.1's copy-in delivers a z as a z rather
// than as "not known". The actual is 4'b10z1, a z being aval 0 with bval 1.
TEST(DpiArgumentPassingInADesign, AnInputActualsHighImpedanceBitIsNotAnX) {
  FourStateActual run(Direction::kInput, SvLogicVecVal{0b1001, 0b0010},
                      SvLogicVecVal{});

  // The bval says bit 1 is unknown, which a two-state crossing cannot say at
  // all. The aval is what separates this from the case above, whose x puts
  // 4'b1011 there; asserted alone it would pass a two-state crossing, which
  // projects 4'b10z1 to the same 4'b1001.
  EXPECT_EQ(run.seen.bval, 0b0010U);
  EXPECT_EQ(run.seen.aval, 0b1001U);
}

// §35.6.1: "For output or inout arguments, the value of the temporary variable
// is assigned to the actual argument with the appropriate conversion." The
// foreign body leaves 4'b0x10 in the formal, so that is what the variable the
// call site named holds once the call has returned.
TEST(DpiArgumentPassingInADesign, AnOutputFormalsUnknownBitReachesTheActual) {
  FourStateActual run(Direction::kOutput, SvLogicVecVal{},
                      SvLogicVecVal{0b0110, 0b0100});

  // aval 4'b0110 with bval 4'b0100 is 4'b0x10. Copied out through one word per
  // bit, bit 2 arrives known and the actual reads 4'b0010.
  EXPECT_EQ(run.Actual().aval, 0b0110U);
  EXPECT_EQ(run.Actual().bval, 0b0100U);
}

}  // namespace

#include <gtest/gtest.h>

#include <cstdint>
#include <utility>
#include <vector>

#include "common/types.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/dpi_runtime.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/svdpi.h"

using namespace delta;

namespace {

// §35.5.5 — Function result. "An imported function declaration shall explicitly
// specify a data type or void for the type of the function's return result.
// Function result types are restricted to small values. The following
// SystemVerilog data types are allowed for imported function results: void,
// byte, shortint, int, longint, real, shortreal, chandle, and string; Scalar
// values of type bit and logic."
//
// The declared type decides what the value a call site receives can hold, and
// these cases ask that of the value a design is actually left with. EvalDpiCall
// in src/simulator/eval_function_dpi.cpp builds it, and §35.2.2.1 rules that
// "The implementation (representation and layout) of 4-state values,
// structures, and arrays is irrelevant for SystemVerilog semantics and can only
// impact the foreign side of the interface", so a result the declared type
// admits has to arrive whatever the carrier between the two sides looks like.

// An import `sv_result()` declared with `kind` as its result type, whose
// foreign body returns `value`. `result` is what the call site `sv_result()` is
// left holding: the width the declared type gives it, and the aval/bval pair
// carrying the value.
struct ImportResultOfType {
  DpiRuntime dpi;
  SimFixture f;
  Logic4Vec result;

  ImportResultOfType(DataTypeKind kind, const DpiArgValue& value) {
    DpiRtFunction func;
    func.c_name = "c_result";
    func.sv_name = "sv_result";
    func.return_type = kind;
    func.impl = [value](const std::vector<DpiArgValue>&) -> DpiArgValue {
      return value;
    };
    dpi.RegisterImport(std::move(func));
    f.ctx.SetDpiRuntime(&dpi);
    result = EvalFunctionCall(ParseExprFrom("sv_result()", f), f.ctx, f.arena);
  }
};

// §35.5.5 admits "Scalar values of type bit and logic" as a result type, and a
// logic has four values, so a body returning x gives the call site x. §35.2.2.1
// leaves the foreign side's representation to the interface, and sv_x is the
// spelling svdpi.h gives x there; an x is aval 1 with bval 1 on this side, and
// a result carried as one word per bit has nowhere to put the bval and gives
// the call site 1.
TEST(DpiFunctionResultInADesign, AScalarLogicResultCarriesAnUnknownBit) {
  ImportResultOfType run(DataTypeKind::kLogic, DpiArgValue::FromLogic(sv_x));

  // The bval is what says the bit is unknown rather than one. The aval is
  // asserted with it because x (1, 1) and z (0, 1) differ in nothing else.
  EXPECT_EQ(run.result.words[0].bval, 1U);
  EXPECT_EQ(run.result.words[0].aval, 1U);
}

// §35.5.5 admits longint as a result type, and a longint is 64 bits, so a body
// returning 0x123456789ABCDEF0 gives the call site all of it. The low 32 bits
// are 0x9ABCDEF0, which the whole value is not: a result assembled at a fixed
// width of 32 keeps those and drops the rest.
TEST(DpiFunctionResultInADesign, ALongintResultCarriesItsUpperWord) {
  ImportResultOfType run(DataTypeKind::kLongint,
                         DpiArgValue::FromLongint(0x123456789ABCDEF0LL));

  EXPECT_EQ(run.result.width, 64U);
  EXPECT_EQ(run.result.words[0].aval, 0x123456789ABCDEF0ULL);
}

// §35.5.5 admits int as a result type, and an int is 32 bits, so the width the
// call site receives is the width the declaration names and not the widest a
// result can travel in. The body returns 0x100000007, whose bit 32 the type
// does not have, so a result built at 64 bits keeps that bit and reads
// 0x100000007 rather than 7.
TEST(DpiFunctionResultInADesign, AnIntResultIsThirtyTwoBitsWide) {
  ImportResultOfType run(DataTypeKind::kInt,
                         DpiArgValue::FromLongint(0x100000007LL));

  EXPECT_EQ(run.result.width, 32U);
  EXPECT_EQ(run.result.words[0].aval, 7U);
}

}  // namespace

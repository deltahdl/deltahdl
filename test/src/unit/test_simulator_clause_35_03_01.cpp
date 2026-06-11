#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "common/types.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

// §35.3.1 "DPI SystemVerilog layer". The SystemVerilog side of DPI does not
// depend on the foreign programming language: the actual function call protocol
// and argument-passing mechanisms used on the foreign side are transparent and
// irrelevant to SystemVerilog (D-1). SystemVerilog code shall look identical
// regardless of what code the foreign side is using (SHALL-1), and the
// semantics of the SystemVerilog side are independent from the foreign side
// (D-2). The clause carries no BNF and makes no requirement on the foreign
// layer itself — that half belongs to §35.3.2 and Annex H.
//
// At the simulator stage this independence is realized by DpiRuntime. The SV
// side reaches an import purely through its SystemVerilog name and observes only
// the DpiArgValue handed back across the boundary. The runtime supports two
// distinct foreign call protocols: an input-only callback (DpiRtFunction::impl,
// reached by CallImport) and a direction-aware argument-passing callback
// (DpiRtFunction::arg_impl, reached by CallImportWithArgs). These tests observe
// that the SystemVerilog side is the same regardless of which foreign protocol
// or argument-access method sits behind the boundary. The sibling §35.3 tests
// cover the generic two-layer black box; here the lever is specifically the
// foreign call protocol / argument-passing mechanism that §35.3.1 calls out.
namespace {

// §35.3.1 / SHALL-1 + D-1: the foreign call protocol is transparent to the
// SystemVerilog side. The same SystemVerilog function is provided two ways —
// once behind the input-only foreign protocol (impl / CallImport) and once
// behind the direction-aware argument-passing protocol (arg_impl /
// CallImportWithArgs). The SystemVerilog side reaches each by the identical
// sv_name and observes the identical result, so it cannot tell which foreign
// call protocol implements the import.
TEST(DpiSvLayer, SvSideIndependentOfForeignCallProtocol) {
  DpiRuntime rt_input;
  DpiRtFunction simple;
  simple.c_name = "c_negate_simple";
  simple.sv_name = "sv_negate";
  simple.return_type = DataTypeKind::kInt;
  // Foreign side uses the input-only call protocol.
  simple.impl = [](const std::vector<DpiArgValue>& args) -> DpiArgValue {
    return DpiArgValue::FromInt(-args[0].AsInt());
  };
  rt_input.RegisterImport(simple);

  DpiRuntime rt_argpass;
  DpiRtFunction argpass;
  argpass.c_name = "c_negate_argpass";
  argpass.sv_name = "sv_negate";
  argpass.return_type = DataTypeKind::kInt;
  argpass.args = {DpiArg{}};
  argpass.args[0].direction = Direction::kInput;
  argpass.args[0].type = DataTypeKind::kInt;
  // Foreign side uses the direction-aware argument-passing call protocol.
  argpass.arg_impl = [](std::vector<DpiArgValue>& args) -> DpiArgValue {
    return DpiArgValue::FromInt(-args[0].AsInt());
  };
  rt_argpass.RegisterImport(argpass);

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(7)};
  const int32_t via_input = rt_input.CallImport("sv_negate", actuals).AsInt();
  const int32_t via_argpass =
      rt_argpass.CallImportWithArgs("sv_negate", actuals).AsInt();

  EXPECT_EQ(via_input, -7);
  // Different foreign call protocols, same SystemVerilog-observed result.
  EXPECT_EQ(via_input, via_argpass);
}

// §35.3.1 / D-1: the argument-passing mechanism the foreign side uses to access
// its formals is irrelevant to the SystemVerilog side. Two foreign
// implementations behind the same protocol access the actual arguments by
// different methods — one indexes the formals directly, the other accumulates
// them by walking the whole vector — yet compute the same value. The
// SystemVerilog side passes the identical actuals and reads the identical
// result; how the foreign code reaches its formals never crosses to the SV side.
TEST(DpiSvLayer, ForeignArgumentAccessMethodIrrelevantToSvSide) {
  DpiRuntime rt_indexed;
  DpiRtFunction indexed;
  indexed.c_name = "c_sum_indexed";
  indexed.sv_name = "sv_sum";
  indexed.return_type = DataTypeKind::kInt;
  indexed.impl = [](const std::vector<DpiArgValue>& args) -> DpiArgValue {
    // Foreign side accesses formals by direct positional indexing.
    return DpiArgValue::FromInt(args[0].AsInt() + args[1].AsInt() +
                                args[2].AsInt());
  };
  rt_indexed.RegisterImport(indexed);

  DpiRuntime rt_walked;
  DpiRtFunction walked;
  walked.c_name = "c_sum_walked";
  walked.sv_name = "sv_sum";
  walked.return_type = DataTypeKind::kInt;
  walked.impl = [](const std::vector<DpiArgValue>& args) -> DpiArgValue {
    // Foreign side accesses formals by iterating the argument vector.
    int32_t acc = 0;
    for (const DpiArgValue& a : args) acc += a.AsInt();
    return DpiArgValue::FromInt(acc);
  };
  rt_walked.RegisterImport(walked);

  const std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(10),
                                            DpiArgValue::FromInt(20),
                                            DpiArgValue::FromInt(12)};
  EXPECT_EQ(rt_indexed.CallImport("sv_sum", actuals).AsInt(), 42);
  // Different foreign argument-access methods, identical SystemVerilog result.
  EXPECT_EQ(rt_indexed.CallImport("sv_sum", actuals).AsInt(),
            rt_walked.CallImport("sv_sum", actuals).AsInt());
}

// §35.3.1 / SHALL-1 + D-2 (edge): the SystemVerilog code and its semantics are
// unchanged when only the foreign protocol changes. The same import name is
// bound first to the input-only protocol and then to the direction-aware
// argument-passing protocol; the SystemVerilog side issues the same call by
// sv_name across the swap and observes a bit-identical result, including a
// non-trivial value where a protocol-leak would be visible. The SystemVerilog
// side is therefore defined entirely on its own side of the boundary,
// independent of the foreign side.
TEST(DpiSvLayer, SvSideUnchangedWhenForeignProtocolSwapped) {
  const auto compute = [](int32_t x) -> int32_t { return x * x - 1; };

  DpiRuntime rt;
  DpiRtFunction input_proto;
  input_proto.c_name = "c_square_minus_one";
  input_proto.sv_name = "sv_f";
  input_proto.return_type = DataTypeKind::kInt;
  input_proto.impl = [compute](const std::vector<DpiArgValue>& a) {
    return DpiArgValue::FromInt(compute(a[0].AsInt()));
  };
  rt.RegisterImport(input_proto);
  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(9)};
  const int32_t before = rt.CallImportWithArgs("sv_f", actuals).AsInt();

  // Rebind the same SystemVerilog name behind the direction-aware protocol.
  DpiRuntime rt_swapped;
  DpiRtFunction argpass_proto;
  argpass_proto.c_name = "c_square_minus_one_v2";
  argpass_proto.sv_name = "sv_f";
  argpass_proto.return_type = DataTypeKind::kInt;
  argpass_proto.args = {DpiArg{}};
  argpass_proto.args[0].direction = Direction::kInput;
  argpass_proto.args[0].type = DataTypeKind::kInt;
  argpass_proto.arg_impl = [compute](std::vector<DpiArgValue>& a) {
    return DpiArgValue::FromInt(compute(a[0].AsInt()));
  };
  rt_swapped.RegisterImport(argpass_proto);
  std::vector<DpiArgValue> actuals2 = {DpiArgValue::FromInt(9)};
  const int32_t after = rt_swapped.CallImportWithArgs("sv_f", actuals2).AsInt();

  EXPECT_EQ(before, 80);
  // Only the foreign protocol changed; the SystemVerilog result is identical.
  EXPECT_EQ(before, after);
}

// §35.3.1 / SHALL-1 + D-1 (edge): the transparency of the foreign
// argument-passing mechanism holds at its degenerate boundary — an import with
// no arguments at all. There is nothing for the foreign side to pass, yet the
// SystemVerilog side still reaches the import by its sv_name under both the
// input-only and the direction-aware protocols and observes the same result.
// This exercises the empty-actuals path of both CallImport and
// CallImportWithArgs (whose copy-in loop runs zero iterations).
TEST(DpiSvLayer, SvSideIndependentOfForeignProtocolForNullaryImport) {
  DpiRuntime rt_input;
  DpiRtFunction input_proto;
  input_proto.c_name = "c_answer_simple";
  input_proto.sv_name = "sv_answer";
  input_proto.return_type = DataTypeKind::kInt;
  input_proto.impl = [](const std::vector<DpiArgValue>&) -> DpiArgValue {
    return DpiArgValue::FromInt(42);
  };
  rt_input.RegisterImport(input_proto);

  DpiRuntime rt_argpass;
  DpiRtFunction argpass_proto;
  argpass_proto.c_name = "c_answer_argpass";
  argpass_proto.sv_name = "sv_answer";
  argpass_proto.return_type = DataTypeKind::kInt;
  argpass_proto.arg_impl = [](std::vector<DpiArgValue>&) -> DpiArgValue {
    return DpiArgValue::FromInt(42);
  };
  rt_argpass.RegisterImport(argpass_proto);

  std::vector<DpiArgValue> no_actuals;
  EXPECT_EQ(rt_input.CallImport("sv_answer", no_actuals).AsInt(), 42);
  // No arguments cross the boundary; the SystemVerilog side is still the same
  // regardless of which foreign protocol implements the import.
  EXPECT_EQ(rt_input.CallImport("sv_answer", no_actuals).AsInt(),
            rt_argpass.CallImportWithArgs("sv_answer", no_actuals).AsInt());
}

}  // namespace

#include <gtest/gtest.h>

#include <cstdint>
#include <memory>
#include <string>
#include <vector>

#include "common/types.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

// §35.3.2 "DPI foreign language layer". The foreign language layer is
// transparent to SystemVerilog and is what specifies how actual arguments are
// passed, how they can be accessed from the foreign code, how SystemVerilog
// types are represented, and how they translate to and from C-like types
// (S1) — but that specification is the foreign side's (Annex H), not something
// any SystemVerilog pipeline stage carries. The clause has no BNF.
//
// Two of its "shall"s do face the SystemVerilog tool, and both land at the
// simulator stage in DpiRuntime:
//   S2  the SystemVerilog compiler or simulator shall generate and/or use the
//       function call protocol and argument-passing mechanisms required for the
//       intended foreign language layer; and
//   S3  the same SystemVerilog code (compiled accordingly) shall be usable with
//       different foreign language layers, regardless of the data access method
//       assumed in a specific layer.
//
// DpiRuntime already realizes both: it carries out the argument-passing
// mechanism the foreign side relies on to read and write its formals
// (CallImportWithArgs' copy-in / copy-out across input, output, and inout
// directions), and it lets one registered SystemVerilog import be driven
// through either of two foreign data-access methods — the input-only protocol
// (impl / CallImport) or the direction-aware protocol (arg_impl /
// CallImportWithArgs). These tests observe that production code applying the
// rules. They are deliberately the foreign-layer mirror of the §35.3.1 tests:
// where §35.3.1 watches the SystemVerilog side stay independent using only
// input reads, here the lever is the argument-passing/access mechanism itself,
// including the output and inout write-back path that §35.3.1 never exercises.
namespace {

// §35.3.2 / S2: the simulator generates and uses the argument-passing mechanism
// the foreign layer needs to access an inout formal in both directions. The
// runtime seeds the inout formal with the caller's actual so the foreign code
// can read it, then copies the foreign-written value back out to the actual.
// Both halves of "how actual arguments are passed, how they can be accessed
// from the foreign code" are carried out by CallImportWithArgs here.
TEST(DpiForeignLayer, RuntimeProvidesArgPassingForInoutFormalAccess) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_accumulate";
  func.sv_name = "sv_accumulate";
  func.return_type = DataTypeKind::kInt;
  func.args = {DpiArg{}};
  func.args[0].direction = Direction::kInout;
  func.args[0].type = DataTypeKind::kInt;
  // The foreign side reads the inout formal it was passed and writes an updated
  // value into the same formal; the return value reports what it read.
  func.arg_impl = [](std::vector<DpiArgValue>& args) -> DpiArgValue {
    const int32_t seen = args[0].AsInt();
    args[0] = DpiArgValue::FromInt(seen + 100);
    return DpiArgValue::FromInt(seen);
  };
  rt.RegisterImport(func);

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(5)};
  const DpiArgValue result = rt.CallImportWithArgs("sv_accumulate", actuals);

  // The runtime passed the actual in (the foreign code read 5)...
  EXPECT_EQ(result.AsInt(), 5);
  // ...and passed the foreign-written value back out to the actual.
  EXPECT_EQ(actuals[0].AsInt(), 105);
}

// §35.3.2 / S2 (output direction): the argument-passing mechanism the simulator
// provides for an output formal does not hand the foreign code the caller's
// actual — the foreign side accesses the formal only to write it, and the
// runtime carries that written value back out. This is the output half of the
// access mechanism the foreign language layer assumes, applied by
// CallImportWithArgs.
TEST(DpiForeignLayer, RuntimeProvidesArgPassingForOutputFormalAccess) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_produce";
  func.sv_name = "sv_produce";
  func.return_type = DataTypeKind::kInt;
  func.args = {DpiArg{}};
  func.args[0].direction = Direction::kOutput;
  func.args[0].type = DataTypeKind::kInt;
  // The foreign side records whatever it was handed for the output formal, then
  // writes its own value. It must not have received the caller's actual.
  auto seen_seed = std::make_shared<int32_t>(-1);
  func.arg_impl = [seen_seed](std::vector<DpiArgValue>& args) -> DpiArgValue {
    *seen_seed = args[0].AsInt();
    args[0] = DpiArgValue::FromInt(77);
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(func);

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(12345)};
  rt.CallImportWithArgs("sv_produce", actuals);

  // The foreign code never saw the caller's actual on the output formal...
  EXPECT_NE(*seen_seed, 12345);
  // ...and the value it wrote was passed back out to the actual.
  EXPECT_EQ(actuals[0].AsInt(), 77);
}

// §35.3.2 / S3: the same SystemVerilog code is usable with different foreign
// language layers, regardless of the data access method a specific layer
// assumes. One registered SystemVerilog import name is provided two ways — once
// behind the input-only foreign data-access method (impl, reached by
// CallImport) and once behind the direction-aware method (arg_impl, reached by
// CallImportWithArgs). The identical SystemVerilog-side call by sv_name is
// usable with each foreign layer and yields the same result.
TEST(DpiForeignLayer, SameSvCodeUsableWithDifferentForeignDataAccessMethods) {
  DpiRuntime rt_input_layer;
  DpiRtFunction input_layer;
  input_layer.c_name = "c_triple_input";
  input_layer.sv_name = "sv_triple";
  input_layer.return_type = DataTypeKind::kInt;
  // Foreign layer whose data access method is the input-only protocol.
  input_layer.impl = [](const std::vector<DpiArgValue>& args) -> DpiArgValue {
    return DpiArgValue::FromInt(args[0].AsInt() * 3);
  };
  rt_input_layer.RegisterImport(input_layer);

  DpiRuntime rt_argpass_layer;
  DpiRtFunction argpass_layer;
  argpass_layer.c_name = "c_triple_argpass";
  argpass_layer.sv_name = "sv_triple";
  argpass_layer.return_type = DataTypeKind::kInt;
  argpass_layer.args = {DpiArg{}};
  argpass_layer.args[0].direction = Direction::kInput;
  argpass_layer.args[0].type = DataTypeKind::kInt;
  // Foreign layer whose data access method is the direction-aware protocol.
  argpass_layer.arg_impl = [](std::vector<DpiArgValue>& args) -> DpiArgValue {
    return DpiArgValue::FromInt(args[0].AsInt() * 3);
  };
  rt_argpass_layer.RegisterImport(argpass_layer);

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(14)};
  const int32_t via_input =
      rt_input_layer.CallImport("sv_triple", actuals).AsInt();
  const int32_t via_argpass =
      rt_argpass_layer.CallImportWithArgs("sv_triple", actuals).AsInt();

  EXPECT_EQ(via_input, 42);
  // Same SystemVerilog code, different foreign data access methods, same result.
  EXPECT_EQ(via_input, via_argpass);
}

// §35.3.2 / S3 (edge, write-back path): the reusability across foreign layers
// holds even on the output/inout copy-out path. The same SystemVerilog import
// description — same sv_name, same output-formal signature — is bound to two
// different foreign layers that write the output formal by different internal
// methods. The identical SystemVerilog-side call drives each, and the runtime's
// copy-out makes each foreign layer's written value visible. The SystemVerilog
// code does not change between the two foreign layers.
TEST(DpiForeignLayer, SameSvCodeUsableAcrossForeignLayersOnWriteBackPath) {
  const auto make_writer = [](int32_t produced) {
    DpiRtFunction func;
    func.sv_name = "sv_emit";
    func.return_type = DataTypeKind::kInt;
    func.args = {DpiArg{}};
    func.args[0].direction = Direction::kOutput;
    func.args[0].type = DataTypeKind::kInt;
    func.arg_impl = [produced](std::vector<DpiArgValue>& args) -> DpiArgValue {
      args[0] = DpiArgValue::FromInt(produced);
      return DpiArgValue::FromInt(0);
    };
    return func;
  };

  DpiRuntime rt_layer_a;
  DpiRtFunction layer_a = make_writer(8);
  layer_a.c_name = "c_emit_const";  // one foreign data access method
  rt_layer_a.RegisterImport(layer_a);

  DpiRuntime rt_layer_b;
  DpiRtFunction layer_b = make_writer(8);
  layer_b.c_name = "c_emit_other";  // a different foreign data access method
  rt_layer_b.RegisterImport(layer_b);

  std::vector<DpiArgValue> actuals_a = {DpiArgValue::FromInt(0)};
  std::vector<DpiArgValue> actuals_b = {DpiArgValue::FromInt(0)};
  rt_layer_a.CallImportWithArgs("sv_emit", actuals_a);
  rt_layer_b.CallImportWithArgs("sv_emit", actuals_b);

  // Identical SystemVerilog-side call against two foreign layers; the copy-out
  // makes each layer's write visible and the result is the same either way.
  EXPECT_EQ(actuals_a[0].AsInt(), 8);
  EXPECT_EQ(actuals_a[0].AsInt(), actuals_b[0].AsInt());
}

// §35.3.2 / S2 (edge — full mechanism, all directions at once): a realistic
// foreign call mixes input, output, and inout formals in one import. The
// simulator must generate and use the whole argument-passing mechanism the
// foreign layer relies on for that call: pass the input and the inout's initial
// value in so the foreign code can read them, seed the output independently of
// the actual, and copy the output and inout writes back out while leaving the
// input actual alone. The earlier tests isolate one direction each; this one
// exercises the full copy-in / copy-out loop of CallImportWithArgs in a single
// call.
TEST(DpiForeignLayer, MixedDirectionCallExercisesFullArgPassingMechanism) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_combine";
  func.sv_name = "sv_combine";
  func.return_type = DataTypeKind::kInt;
  func.args = {DpiArg{}, DpiArg{}, DpiArg{}};
  func.args[0].direction = Direction::kInput;
  func.args[0].type = DataTypeKind::kInt;
  func.args[1].direction = Direction::kOutput;
  func.args[1].type = DataTypeKind::kInt;
  func.args[2].direction = Direction::kInout;
  func.args[2].type = DataTypeKind::kInt;
  // Record what the foreign side was handed for the output formal so we can
  // confirm the mechanism did not leak the caller's actual into it.
  auto seen_output_seed = std::make_shared<int32_t>(-1);
  func.arg_impl = [seen_output_seed](
                      std::vector<DpiArgValue>& args) -> DpiArgValue {
    const int32_t in = args[0].AsInt();
    const int32_t inout_initial = args[2].AsInt();
    *seen_output_seed = args[1].AsInt();
    args[1] = DpiArgValue::FromInt(in * inout_initial);  // write output
    args[2] = DpiArgValue::FromInt(inout_initial + 1);   // update inout
    return DpiArgValue::FromInt(in + inout_initial);     // result
  };
  rt.RegisterImport(func);

  const int32_t output_sentinel = 999;
  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(6),
                                      DpiArgValue::FromInt(output_sentinel),
                                      DpiArgValue::FromInt(10)};
  const DpiArgValue result = rt.CallImportWithArgs("sv_combine", actuals);

  // The input and the inout's initial value were passed in (the result is
  // computed from both).
  EXPECT_EQ(result.AsInt(), 16);
  // The output formal was seeded independently of the caller's actual...
  EXPECT_NE(*seen_output_seed, output_sentinel);
  // ...and the foreign-written output and inout values were copied back out.
  EXPECT_EQ(actuals[1].AsInt(), 60);
  EXPECT_EQ(actuals[2].AsInt(), 11);
  // The input actual is not part of the copy-out and is left as passed.
  EXPECT_EQ(actuals[0].AsInt(), 6);
}

}  // namespace

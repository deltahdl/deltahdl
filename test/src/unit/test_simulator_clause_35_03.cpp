#include <gtest/gtest.h>

#include <cstdint>
#include <memory>
#include <string>
#include <vector>

#include "simulator/dpi_runtime.h"

using namespace delta;

// §35.3 "Two layers of DPI". DPI is split into a SystemVerilog layer and a
// foreign language layer. The SystemVerilog layer does not depend on which
// programming language sits behind the boundary: SystemVerilog code shall look
// identical and its semantics shall be unchanged for any foreign language
// layer, and the implementation need only support C protocols and linkage.
//
// At the simulator stage that two-layer split is realized by DpiRuntime: the
// SystemVerilog side reaches an import purely through its SystemVerilog name
// and observes only the result handed back across the boundary. The foreign
// (C) implementation is an opaque callback. These tests observe that black-box
// separation; the spec-string and linkage-name syntax that name the C layer
// belong to §35.4 and §35.5.4, not here.
namespace {

// §35.3 / S5: the SystemVerilog layer reaches the foreign side through the
// import's SystemVerilog name and the foreign implementation is an ordinary C
// callback. The call crosses the boundary and the SystemVerilog side sees only
// the value the foreign layer returns.
TEST(DpiTwoLayers, SvLayerCallsForeignImplBySvName) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_add_one";
  func.sv_name = "sv_add_one";
  func.impl = [](const std::vector<DpiArgValue>& args) -> DpiArgValue {
    return DpiArgValue::FromInt(args[0].AsInt() + 1);
  };
  rt.RegisterImport(func);

  const DpiArgValue kResult =
      rt.CallImport("sv_add_one", {DpiArgValue::FromInt(41)});
  EXPECT_EQ(kResult.AsInt(), 42);
}

// §35.3 / S1, S2, S4: SystemVerilog code shall look identical and its semantics
// shall be unchanged for any foreign language layer. Two distinct foreign
// implementations that compute the same result are indistinguishable to the
// SystemVerilog caller: the same SystemVerilog-side call yields the same value,
// so the SystemVerilog layer cannot tell which foreign implementation is behind
// the boundary.
TEST(DpiTwoLayers, ForeignImplIsOpaqueToSvLayer) {
  DpiRuntime rt_a;
  DpiRtFunction direct;
  direct.c_name = "c_double_direct";
  direct.sv_name = "sv_double";
  direct.impl = [](const std::vector<DpiArgValue>& args) -> DpiArgValue {
    return DpiArgValue::FromInt(args[0].AsInt() * 2);
  };
  rt_a.RegisterImport(direct);

  DpiRuntime rt_b;
  DpiRtFunction by_addition;
  by_addition.c_name = "c_double_by_addition";
  by_addition.sv_name = "sv_double";
  by_addition.impl = [](const std::vector<DpiArgValue>& args) -> DpiArgValue {
    const int32_t kX = args[0].AsInt();
    return DpiArgValue::FromInt(kX + kX);
  };
  rt_b.RegisterImport(by_addition);

  const std::vector<DpiArgValue> kActual = {DpiArgValue::FromInt(21)};
  // Identical SystemVerilog-side call, two different foreign implementations:
  // the SystemVerilog layer observes the same result either way.
  EXPECT_EQ(rt_a.CallImport("sv_double", kActual).AsInt(),
            rt_b.CallImport("sv_double", kActual).AsInt());
}

// §35.3 / S1: the SystemVerilog layer does not depend on the foreign linkage
// symbol. An import is resolved by its SystemVerilog name; the foreign c_name
// is the foreign layer's concern. Two imports sharing a c_name but bound to
// distinct SystemVerilog names dispatch independently, and the SystemVerilog
// side never consults the c_name to make the call.
TEST(DpiTwoLayers, SvLayerResolvesBySvNameNotForeignSymbol) {
  DpiRuntime rt;
  DpiRtFunction lo;
  lo.c_name = "c_shared";
  lo.sv_name = "sv_lo";
  lo.impl = [](const std::vector<DpiArgValue>&) -> DpiArgValue {
    return DpiArgValue::FromInt(1);
  };
  rt.RegisterImport(lo);

  DpiRtFunction hi;
  hi.c_name = "c_shared";  // same foreign symbol name
  hi.sv_name = "sv_hi";    // distinct SystemVerilog name
  hi.impl = [](const std::vector<DpiArgValue>&) -> DpiArgValue {
    return DpiArgValue::FromInt(2);
  };
  rt.RegisterImport(hi);

  EXPECT_EQ(rt.CallImport("sv_lo", {}).AsInt(), 1);
  EXPECT_EQ(rt.CallImport("sv_hi", {}).AsInt(), 2);
}

// §35.3 / S1, S2, S4 (edge case): whatever the foreign layer does behind the
// boundary is opaque to the SystemVerilog layer. A foreign implementation that
// keeps private state across calls exposes none of it to the SystemVerilog
// side; each call's result reflects only the value handed back. The
// SystemVerilog semantics therefore depend solely on the data crossing the
// boundary, never on the foreign side's internal mechanism — so they stay
// unchanged no matter how the foreign layer is built.
TEST(DpiTwoLayers, ForeignInternalStateIsOpaqueToSvLayer) {
  DpiRuntime rt;
  DpiRtFunction counter;
  counter.c_name = "c_next";
  counter.sv_name = "sv_next";
  // Private foreign-side state captured in the callback; the SystemVerilog
  // layer has no handle to it and can only observe the returned values.
  auto ticks = std::make_shared<int32_t>(0);
  counter.impl = [ticks](const std::vector<DpiArgValue>&) -> DpiArgValue {
    return DpiArgValue::FromInt(++(*ticks));
  };
  rt.RegisterImport(counter);

  // The SystemVerilog side sees only successive returned values; the foreign
  // counter itself is never visible across the boundary.
  EXPECT_EQ(rt.CallImport("sv_next", {}).AsInt(), 1);
  EXPECT_EQ(rt.CallImport("sv_next", {}).AsInt(), 2);
  EXPECT_EQ(rt.CallImport("sv_next", {}).AsInt(), 3);
}

}  // namespace

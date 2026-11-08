#include <gtest/gtest.h>

#include <cstdint>
#include <memory>
#include <string>
#include <vector>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

namespace {

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
  EXPECT_EQ(rt_a.CallImport("sv_double", kActual).AsInt(),
            rt_b.CallImport("sv_double", kActual).AsInt());
}

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
  hi.c_name = "c_shared";
  hi.sv_name = "sv_hi";
  hi.impl = [](const std::vector<DpiArgValue>&) -> DpiArgValue {
    return DpiArgValue::FromInt(2);
  };
  rt.RegisterImport(hi);

  EXPECT_EQ(rt.CallImport("sv_lo", {}).AsInt(), 1);
  EXPECT_EQ(rt.CallImport("sv_hi", {}).AsInt(), 2);
}

TEST(DpiTwoLayers, ForeignInternalStateIsOpaqueToSvLayer) {
  DpiRuntime rt;
  DpiRtFunction counter;
  counter.c_name = "c_next";
  counter.sv_name = "sv_next";
  auto ticks = std::make_shared<int32_t>(0);
  counter.impl = [ticks](const std::vector<DpiArgValue>&) -> DpiArgValue {
    return DpiArgValue::FromInt(++(*ticks));
  };
  rt.RegisterImport(counter);

  EXPECT_EQ(rt.CallImport("sv_next", {}).AsInt(), 1);
  EXPECT_EQ(rt.CallImport("sv_next", {}).AsInt(), 2);
  EXPECT_EQ(rt.CallImport("sv_next", {}).AsInt(), 3);
}

TEST(DpiTwoLayers, ExportedSvBodyIsUnchangedByWhichForeignEntryCallsIt) {
  DpiRuntime rt;
  DpiRtExport exp;
  exp.c_name = "c_scale";
  exp.sv_name = "sv_scale";
  exp.return_type = DataTypeKind::kInt;
  exp.args = {DpiArg{"x", DataTypeKind::kInt, Direction::kInput}};
  exp.impl = [](const std::vector<DpiArgValue>& args) {
    return DpiArgValue::FromInt(args[0].AsInt() * 3);
  };
  rt.RegisterExport(exp);

  const DpiArgValue kDirect =
      rt.CallExport("sv_scale", {DpiArgValue::FromInt(14)});

  DpiScope scope;
  scope.name = "top";
  rt.EnterContextImportCall("ctx_import", scope);
  DpiArgValue from_import;
  rt.CallExportFromImport("sv_scale", {DpiArgValue::FromInt(14)}, &from_import);

  EXPECT_EQ(kDirect.AsInt(), 42);
  EXPECT_EQ(from_import.AsInt(), 42);
}

}  // namespace

#include <gtest/gtest.h>

#include <cstdint>
#include <utility>
#include <vector>

#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

namespace {

DpiRuntime RuntimeWithExport(DpiRtCallback export_body) {
  DpiRuntime rt;
  DpiRtFunction ctx;
  ctx.c_name = "c_ctx";
  ctx.sv_name = "ctx_import";
  ctx.is_context = true;
  ctx.impl = [](const std::vector<DpiArgValue>&) {
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(ctx);
  DpiRtFunction plain;
  plain.c_name = "c_plain";
  plain.sv_name = "plain_import";
  plain.impl = [](const std::vector<DpiArgValue>&) {
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(plain);
  DpiRtExport exported;
  exported.c_name = "c_exp";
  exported.sv_name = "sv_exp";
  exported.scope_name = "top";
  exported.impl = std::move(export_body);
  rt.RegisterExport(exported);
  return rt;
}

DpiScope Top() {
  DpiScope scope;
  scope.name = "top";
  return scope;
}

TEST(DpiContextCallChain, AChainStartsWhenSystemVerilogCallsAnImport) {
  DpiRuntime rt = RuntimeWithExport(nullptr);
  EXPECT_FALSE(rt.InCallChain());
  EXPECT_FALSE(rt.InContextCallChain());
  EXPECT_EQ(rt.OpenCallChainCount(), 0u);
  rt.EnterDeclaredImportCall("ctx_import", Top());
  EXPECT_TRUE(rt.InCallChain());
  EXPECT_TRUE(rt.InContextCallChain());
  EXPECT_EQ(rt.OpenCallChainCount(), 1u);
  rt.LeaveImportCall();
  EXPECT_FALSE(rt.InCallChain());
  EXPECT_EQ(rt.OpenCallChainCount(), 0u);
}

TEST(DpiContextCallChain, ANoncontextImportOpensNoContextChain) {
  DpiRuntime rt = RuntimeWithExport(nullptr);
  rt.EnterDeclaredImportCall("plain_import", Top());
  EXPECT_TRUE(rt.InCallChain());
  EXPECT_FALSE(rt.InContextCallChain());
  rt.LeaveImportCall();
}

struct Observed {
  bool in_chain_before = true;
  uint32_t open_before = 0;
  bool in_chain_inside = false;
  bool context_inside = true;
  uint32_t open_inside = 0;
};

TEST(DpiContextCallChain, AnExportCallEndsTheChainAndItsImportsStartAnother) {
  Observed observed;
  DpiRuntime* runtime = nullptr;
  DpiRuntime rt =
      RuntimeWithExport([&observed, &runtime](const std::vector<DpiArgValue>&) {
        observed.in_chain_before = runtime->InCallChain();
        observed.open_before = runtime->OpenCallChainCount();
        runtime->EnterDeclaredImportCall("plain_import", Top());
        observed.in_chain_inside = runtime->InCallChain();
        observed.context_inside = runtime->InContextCallChain();
        observed.open_inside = runtime->OpenCallChainCount();
        runtime->LeaveImportCall();
        return DpiArgValue::FromInt(0);
      });
  runtime = &rt;
  rt.EnterDeclaredImportCall("ctx_import", Top());
  DpiArgValue result;
  EXPECT_EQ(rt.CallExportFromImport("sv_exp", {}, &result),
            DpiExportCallStatus::kOk);
  EXPECT_FALSE(observed.in_chain_before);
  EXPECT_EQ(observed.open_before, 1u);
  EXPECT_TRUE(observed.in_chain_inside);
  EXPECT_FALSE(observed.context_inside);
  EXPECT_EQ(observed.open_inside, 2u);
  EXPECT_TRUE(rt.InCallChain());
  EXPECT_TRUE(rt.InContextCallChain());
  EXPECT_EQ(rt.OpenCallChainCount(), 1u);
  rt.LeaveImportCall();
}

TEST(DpiContextCallChain, TheContextPropertyIsTheInnermostImports) {
  DpiRuntime rt = RuntimeWithExport(nullptr);
  rt.EnterDeclaredImportCall("ctx_import", Top());
  rt.EnterDeclaredImportCall("plain_import", Top());
  EXPECT_TRUE(rt.InCallChain());
  EXPECT_FALSE(rt.InContextCallChain());
  EXPECT_EQ(rt.OpenCallChainCount(), 1u);
  rt.LeaveImportCall();
  EXPECT_TRUE(rt.InContextCallChain());
  rt.LeaveImportCall();
}

}  // namespace
